import Lean
import Lean.Elab.Tactic

import Loom.MonadAlgebras.WP.Attr
import Loom.MonadAlgebras.WP.Basic
import Loom.MonadAlgebras.NonDetT.Basic

import Mathlib.Tactic.Common

open Lean.Expr hiding fvar
open Lean Lean.Meta
open Elab.Term hiding observing
open Lean Elab Command Meta Tactic

open Tactic Lean.Meta

private def resolveSimpIdTheorem? (simpArgTerm : Term) : TermElabM ResolveSimpIdResult := do
    let resolveExt (n : Name) : TermElabM ResolveSimpIdResult := do
      let ext₁? ← getSimpExtension? n
      let ext₂? ← Simp.getSimprocExtension? n
      if h : ext₁?.isSome || ext₂?.isSome then
        return .ext ext₁? ext₂? h
      else
        return .none
    match simpArgTerm with
    | `($id:ident) =>
      try
        if let some e ← Term.resolveId? simpArgTerm (withInfo := true) then
          if let some simprocDeclName ← isSimproc? e then
            return .simproc simprocDeclName
          else
            return .expr e
        else
          let name := id.getId.eraseMacroScopes
          if (← Simp.isBuiltinSimproc name) then
            return .simproc name
          else
            resolveExt name
      catch _ =>
        resolveExt id.getId.eraseMacroScopes
    | _ =>
      if let some e ← Term.elabCDotFunctionAlias? simpArgTerm then
        return .expr e
      else
        return .none
where
  isSimproc? (e : Expr) : MetaM (Option Name) := do
    let .const declName _ := e | return none
    unless (← Simp.isSimproc declName) do return none
    return some declName

/-- Implements the effect of the `*` attribute. -/
private def applyStarArg (ctx : Simp.Context) : MetaM Simp.Context := do
  let mut simpTheorems := ctx.simpTheorems
  /-
  When using `zetaDelta := false`, we do not expand let-declarations when using `[*]`.
  Users must explicitly include it in the list.
  -/
  let hs ← getPropHyps
  for h in hs do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr (config := ctx.indexConfig)
  return ctx.setSimpTheorems simpTheorems

private def elabDeclToUnfoldOrTheorem (config : Meta.ConfigWithKey) (id : Origin)
    (e : Expr) (post : Bool) (inv : Bool) (kind : SimpKind) : MetaM ElabSimpArgResult := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstVal declName
    if (← isProp info.type) then
      let thms ← mkSimpTheoremFromConst declName (post := post) (inv := inv)
      return .addEntries <| thms.map (SimpEntry.thm ·)
    else
      if inv then
        throwError m!"Invalid `←` modifier: `{declName}` is a declaration name to be unfolded"
          ++ .hint' m!"The simplifier cannot \"refold\" definitions by name. Use `rw` for this intead,
                      or use the `←` simp modifier with an equational lemma for `{declName}`."
      if kind == .dsimp then
        return .addEntries #[.toUnfold declName]
      else
        .addEntries <$> mkSimpEntryOfDeclToUnfold declName
  else if e.isFVar then
    let fvarId := e.fvarId!
    let decl ← fvarId.getDecl
    if (← isProp decl.type) then
      let thms ← mkSimpTheoremFromExpr id #[] e (post := post) (inv := inv) (config := config)
      return .addEntries <| thms.map (SimpEntry.thm ·)
    else if !decl.isLet then
      throwError "Invalid argument: Variable `{e}` is not a proposition or let-declaration"
    else if inv then
      throwError m!"Invalid `←` modifier: `{e}` is a let-declaration name to be unfolded"
        ++ .note "The simplifier cannot \"refold\" local declarations by name"
    else
      return .addLetToUnfold fvarId
  else
    let thms ← mkSimpTheoremFromExpr id #[] e (post := post) (inv := inv) (config := config)
    return .addEntries <| thms.map (SimpEntry.thm ·)

private def elabSimpTheorem (config : Meta.ConfigWithKey) (id : Origin) (stx : Syntax)
    (post : Bool) (inv : Bool) : TermElabM ElabSimpArgResult := do
  let thm? ← Term.withoutModifyingElabMetaStateWithInfo <| withRef stx do
    let e ← Term.elabTerm stx .none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    if e.hasSyntheticSorry then
      return .none
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return some (r.paramNames, r.expr)
    else
      return some (#[], e)
  if let some (levelParams, proof) := thm? then
    let thms ← mkSimpTheoremFromExpr id levelParams proof (post := post) (inv := inv) (config := config)
    return .addEntries <| thms.map (SimpEntry.thm ·)
  else
    return .none

private def elabSimpArg (indexConfig : Meta.ConfigWithKey) (eraseLocal : Bool) (kind : SimpKind)
    (arg : Syntax) : TermElabM ElabSimpArgResult := withRef arg do
  try
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? "← "? term

    syntax simpErase := "-" ident
    -/
    if arg.getKind == ``Lean.Parser.Tactic.simpErase then
      let fvar? ← if eraseLocal then Term.isLocalIdent? arg[1] else pure none
      if let some fvar := fvar? then
        -- We use `eraseCore` because the simp theorem for the hypothesis was not added yet
        return .erase (.fvar fvar.fvarId!)
      else
        let id := arg[1]
        if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
          if (← Simp.isSimproc declName) then
            return .eraseSimproc declName
          else
            return .erase (.decl declName)
        else
          -- If `id` could not be resolved, we should check whether it is a builtin simproc.
          -- before returning error.
          let name := id.getId.eraseMacroScopes
          if (← Simp.isBuiltinSimproc name) then
            return .eraseSimproc name
          else
            throwUnknownConstantAt id name
    else if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
      let post :=
        if arg[0].isNone then
          true
        else
          arg[0][0].getKind == ``Parser.Tactic.simpPost
      let inv  := !arg[1].isNone
      let term := arg[2]
      match (← resolveSimpIdTheorem? ⟨term⟩) with
      | .expr e  =>
        let name ← mkFreshId
        elabDeclToUnfoldOrTheorem indexConfig (.stx name arg) e post inv kind
      | .simproc declName =>
        return .addSimproc declName post
      | .ext ext₁? ext₂? h =>
        return .ext ext₁? ext₂? h
      | .none    =>
        let name ← mkFreshId
        elabSimpTheorem indexConfig (.stx name arg) term post inv
    else if arg.getKind == ``Lean.Parser.Tactic.simpStar then
      return .star
    else
      throwUnsupportedSyntax
  catch ex =>
    throw ex


/--
  Elaborate extra simp theorems provided to `simp`. `stx` is of the form `"[" simpTheorem,* "]"`
  If `eraseLocal == true`, then we consider local declarations when resolving names for erased theorems (`- id`),
  this option only makes sense for `simp_all` or `*` is used.
  When `recover := true`, try to recover from errors as much as possible so that users keep seeing
  the current goal.
-/
def elabSimpArgs' (stx : Syntax) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray) (eraseLocal : Bool)
    (kind : SimpKind) (ignoreStarArg := false) : TermElabM ElabSimpArgsResult := do
  if stx.isNone then
    return { ctx, simprocs, simpArgs := #[] }
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? "← "? term

    syntax simpErase := "-" ident
    -/
    let go := do -- withMainContext do
      let zetaDeltaSet ← toZetaDeltaSet stx ctx
      withTrackingZetaDeltaSet zetaDeltaSet do
        let mut starArg := false -- only after * we can erase local declarations
        let mut args : Array (Syntax × ElabSimpArgResult) := #[]
        for argStx in stx[1].getSepArgs do
          let arg ← elabSimpArg ctx.indexConfig (eraseLocal || starArg) kind argStx
          starArg := !ignoreStarArg && (starArg || arg matches .star)
          args := args.push (argStx, arg)

        let mut thmsArray := ctx.simpTheorems
        let mut thms      := thmsArray[0]!
        let mut simprocs  := simprocs
        for (ref, arg) in args do
          match arg with
          | .addEntries entries =>
            for entry in entries do
              thms := thms.uneraseSimpEntry entry
              thms := thms.addSimpEntry entry
          | .addLetToUnfold fvarId =>
            thms := thms.addLetDeclToUnfold fvarId
          | .addSimproc declName post =>
            simprocs ← simprocs.add declName post
          | .erase origin =>
            -- `thms.erase` checks if the erasure is effective.
            -- We do not want this check for local hypotheses (they are added later based on `starArg`)
            if origin matches .fvar _ then
              thms := thms.eraseCore origin
            -- Nor for decls to unfold when we do auto unfolding
            else if ctx.config.autoUnfold then
              thms := thms.eraseCore origin
            else
              thms ← withRef ref <| thms.erase origin
          | .eraseSimproc name =>
            simprocs := simprocs.erase name
          | .ext simpExt? simprocExt? _ =>
            if let some simpExt := simpExt? then
              thmsArray := thmsArray.push (← simpExt.getTheorems)
            if let some simprocExt := simprocExt? then
              simprocs := simprocs.push (← simprocExt.getSimprocs)
          | .star => pure ()
          | .none => pure ()

        let mut ctx := ctx.setZetaDeltaSet zetaDeltaSet (← getZetaDeltaFVarIds)
        ctx := ctx.setSimpTheorems (thmsArray.set! 0 thms)
        if !ignoreStarArg && starArg then
          ctx ← applyStarArg ctx

        return { ctx, simprocs, simpArgs := args}
    -- If recovery is disabled, then we want simp argument elaboration failures to be exceptions.
    -- This affects `addSimpTheorem`.
    Term.withoutErrToSorry go
where
  /-- If `zetaDelta := false`, create a `FVarId` set with all local let declarations in the `simp` argument list. -/
  toZetaDeltaSet (stx : Syntax) (ctx : Simp.Context) : TermElabM FVarIdSet := do
    if ctx.config.zetaDelta then return {}
    Term.withoutCheckDeprecated do -- We do not want to report deprecated constants in the first pass
      let mut s : FVarIdSet := {}
      for arg in stx[1].getSepArgs do
        if arg.getKind == ``Lean.Parser.Tactic.simpLemma then
          if arg[0].isNone && arg[1].isNone then
            let term := arg[2]
            let .expr (.fvar fvarId) ← resolveSimpIdTheorem? ⟨term⟩ | pure ()
            if (← fvarId.getDecl).isLet then
              s := s.insert fvarId
      return s

/--
  Implement a `simp` discharge function using the given tactic syntax code.
  Recall that `simp` dischargers are in `SimpM` which does not have access to `Term.State`.
  We need access to `Term.State` to store messages and update the info tree.
  Thus, we create an `IO.ref` to track these changes at `Term.State` when we execute `tacticCode`.
  We must set this reference with the current `Term.State` before we execute `simp` using the
  generated `Simp.Discharge`. -/
def tacticToDischarge (tacticCode : Syntax) : TermElabM (IO.Ref Term.State × Simp.Discharge) := do
  let tacticCode ← `(tactic| try ($(⟨tacticCode⟩):tacticSeq))
  let ref ← IO.mkRef (← getThe Term.State)
  let ctx ← readThe Term.Context
  let disch : Simp.Discharge := fun e => do
    let mvar ← mkFreshExprSyntheticOpaqueMVar e `simp.discharger
    let s ← ref.get
    let runTac? : TermElabM (Option Expr) :=
      try
        /- We must only save messages and info tree changes. Recall that `simp` uses temporary metavariables (`withNewMCtxDepth`).
           So, we must not save references to them at `Term.State`.
        -/
        withoutModifyingStateWithInfoAndMessages do
          Term.withSynthesize (postpone := .no) do
            Term.runTactic (report := false) mvar.mvarId! tacticCode .term
          let result ← instantiateMVars mvar
          if result.hasExprMVar then
            return none
          else
            return some result
      catch _ =>
        return none
    let (result?, s) ← liftM (m := MetaM) <| Term.TermElabM.run runTac? ctx s
    ref.set s
    return result?
  return (ref, disch)

/-- Construct a `Simp.DischargeWrapper` from the `Syntax` for a `simp` discharger. -/
private def mkDischargeWrapper (optDischargeSyntax : Syntax) : TermElabM Simp.DischargeWrapper := do
  if optDischargeSyntax.isNone then
    return Simp.DischargeWrapper.default
  else
    let (ref, d) ← tacticToDischarge optDischargeSyntax[0][3]
    return Simp.DischargeWrapper.custom ref d

@[inline] def simpOnlyBuiltins' : List Name := [``eq_self, ``iff_self]
/--
   Create the `Simp.Context` for the `simp`, `dsimp`, and `simp_all` tactics.
   If `kind != SimpKind.simp`, the `discharge` option must be `none`

   TODO: generate error message if non `rfl` theorems are provided as arguments to `dsimp`.

   The argument `simpTheorems` defaults to `getSimpTheorems`,
   but allows overriding with an arbitrary mechanism to choose
   the simp theorems besides those specified in the syntax.
   Note that if the syntax includes `simp only`, the `simpTheorems` argument is ignored.
-/
def mkSimpContext' (stx : Syntax) (eraseLocal : Bool) (kind := SimpKind.simp)
    (ignoreStarArg : Bool := false) (simpTheorems : CoreM SimpTheorems := getSimpTheorems) :
    TermElabM MkSimpContextResult := do
  if !stx[2].isNone then
    if kind == SimpKind.simpAll then
      throwError "Tactic `simp_all` does not support the `discharger` option"
    if kind == SimpKind.dsimp then
      throwError "Tactic `dsimp` does not support the `discharger' option"
  let dischargeWrapper ← mkDischargeWrapper stx[2]
  let simpOnly := !stx[simpOnlyPos].isNone
  let simpTheorems ← if simpOnly then
    simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  else
    simpTheorems
  let simprocs ← if simpOnly then pure {} else Simp.getSimprocs
  let congrTheorems ← getSimpCongrTheorems
  let ctx ← Simp.mkContext
     (config := { dsimp := kind == .dsimp })
     (simpTheorems := #[simpTheorems])
     congrTheorems
  let r ← elabSimpArgs' stx[4] (eraseLocal := eraseLocal) (kind := kind) (simprocs := #[simprocs]) (ignoreStarArg := ignoreStarArg) ctx
  return { r with dischargeWrapper }

def Lean.Expr.runSimp (e : Expr) (stx : TermElabM (TSyntax `tactic)) : TermElabM Simp.Result := do
  let ctx <- mkSimpContext' (← stx) false
  let res <- simp e ctx.ctx (simprocs := ctx.simprocs) (discharge? := none)
  return res.1

def Lean.Expr.runUnfold (e : Expr) (defs : List Name) : TermElabM Expr := do
  let mut eu := e
  for name in defs do eu := (<- unfold eu name).expr
  return eu

def ultimateReduce (e : Expr) : TermElabM Expr :=
  withTransparency (mode := .default) <| reduceAll e

def simpleAddThm (n : Name) (tp : Expr) (pf : Expr)
  (attr : Array Attribute := #[]) : TermElabM Unit := do
  addDecl <|
    Declaration.thmDecl <|
      mkTheoremValEx n [] tp pf []
  applyAttributes n attr

elab "#reduce!" e:term : command => do
  liftTermElabM do
    let e ← ultimateReduce <| <- Term.elabTerm e none
    logInfoAt (<- getRef) e

macro "forall?" br:bracketedBinder* "," t:term : term =>
  if br.size > 0 then
    `(∀ $br*, $t)
  else
    `($t)

def toIdent (bi : TSyntax ``binderIdent) : Ident :=
  match bi with
  | `(binderIdent|$i:ident) => i
  | _ => unreachable!

def toBracketedBinderArray (stx : TSyntax `Lean.explicitBinders) : MetaM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
  let mut binders := #[]
  match stx with
  | `(explicitBinders|$bs*) => do
    binders := binders.append (← bs.mapM helper)
  | _ => throwError "unexpected syntax in explicit binder: {stx}"
  return binders.flatten
  where
  helper (stx : TSyntax `Lean.bracketedExplicitBinders) : MetaM (TSyntaxArray `Lean.Parser.Term.bracketedBinder) := do
    let mut binders := #[]
    match stx with
    | `(bracketedExplicitBinders|($bis* : $tp)) => do
      for bi in bis do
        let id := toIdent bi
        let fb ← `(bracketedBinder| ($id : $tp:term))
        binders := binders.push fb
      pure ()
    | _ => throwError "unexpected syntax in explicit binder: {stx}"
    return binders

def toFunBinderArray (stx : TSyntax `Lean.explicitBinders) : MetaM (TSyntaxArray `Lean.Parser.Term.funBinder) := do
  let mut binders := #[]
  match stx with
  | `(explicitBinders|$bs*) => do
    binders := binders.append (← bs.mapM helper)
  | _ => throwError "unexpected syntax in explicit binder: {stx}"
  return binders.flatten
  where
  helper (stx : TSyntax `Lean.bracketedExplicitBinders) : MetaM (TSyntaxArray `Lean.Parser.Term.funBinder) := do
    let mut binders := #[]
    match stx with
    | `(bracketedExplicitBinders|($bis* : $tp)) => do
      for bi in bis do
        let id := toIdent bi
        let fb ← `(Lean.Parser.Term.funBinder| ($id : $tp:term))
        binders := binders.push fb
      pure ()
    | _ => throwError "unexpected syntax in explicit binder: {stx}"
    return binders

def existentialIdents (stx : TSyntax `Lean.explicitBinders) : MetaM (TSyntaxArray `term) := do
  let mut vars := #[]
  match stx with
  | `(explicitBinders|$bs*) => do
    for b in bs do
      match b with
      | `(bracketedExplicitBinders|($bis* : $_tp)) => do
        for bi in bis do
          let id := toIdent bi
          vars := vars.push id
      | _ => throwError "unexpected syntax in explicit binder: {b}"
  | _ => throwError "unexpected syntax in explicit binder: {stx}"
  return vars

-- register_simp_attr loomWpSimp

elab "#gen_spec" name:ident args:explicitBinders ? "for" prim:term : command => do
  liftTermElabM do
    let ⟨funArgs, forallArgs, args⟩ <-
      match args with
      | .some args => do
        let funArgs    <- toFunBinderArray args
        let forallArgs <- toBracketedBinderArray args
        let args       <- existentialIdents args
        pure (funArgs, forallArgs, args)
      | .none => pure (#[], #[], #[])
    let primFun <- `(fun $funArgs* => $prim)
    let primExp <- elabTermAndSynthesize primFun none
    let (pf, primRed) <- lambdaTelescope primExp fun args primExp => do
      let primRed <- ultimateReduce primExp
      let ⟨primRed, prf, _⟩ <- Expr.runSimp primRed <| `(tactic| simp)
      let pf := prf.getD <| <- mkAppM ``Eq.refl #[primExp]
      let pf <- mkLambdaFVars args pf
      let primRed <- mkLambdaFVars args primRed
      return (pf, primRed)
    let primRed <- Term.exprToSyntax primRed
    let tp := <- elabTermAndSynthesize (<- `(forall? $forallArgs*, $prim = $primRed $args*)) none
    let ⟨tp, _, _⟩ <- Expr.runSimp tp <| `(tactic| dsimp only)
    let module <- getCurrNamespace
    simpleAddThm (module ++ name.getId) tp pf (attr := #[{name := `loomWpSimp} ])
    trace[debug] "Generated spec for {prim}:\n{tp}"

attribute [loomLogicLiftSimp]
  LogicLiftT.lift
  instMonadLiftTOfMonadLift
  instMonadLiftContOfLogicLift
  MAlgLift.cl
  LogicLift.refl
  instMonadLiftTContOfLogicLiftT
  instMonadLiftT
  id

attribute [loomWPGenRewrite]
  StateT.wp_get
  StateT.wp_set
  StateT.wp_modifyGet
  ExceptT.wp_throw
  ReaderT.wp_read
  MAlgLift.wp_throw

  TotalCorrectness.AngelicChoice.MonadNonDet.wp_pickSuchThat
  TotalCorrectness.DemonicChoice.MonadNonDet.wp_pickSuchThat
  PartialCorrectness.AngelicChoice.MonadNonDet.wp_pickSuchThat
  PartialCorrectness.DemonicChoice.MonadNonDet.wp_pickSuchThat

  TotalCorrectness.DemonicChoice.MonadNonDet.wp_assume
  TotalCorrectness.AngelicChoice.MonadNonDet.wp_assume
  TotalCorrectness.DemonicChoice.MonadNonDet.wp_pick
  TotalCorrectness.AngelicChoice.MonadNonDet.wp_pick
  PartialCorrectness.DemonicChoice.MonadNonDet.wp_assume
  PartialCorrectness.AngelicChoice.MonadNonDet.wp_assume
  PartialCorrectness.DemonicChoice.MonadNonDet.wp_pick
  PartialCorrectness.AngelicChoice.MonadNonDet.wp_pick


elab "#derive_lifted_wp" args:explicitBinders ? "for" "(" name:term ":" type:term ")" "as" m:ident out:ident : command => do
  let args_list ← liftTermElabM do
    match args with
    | .some args => do
      toBracketedBinderArray args
    | .none => pure #[]
  let wp_name ← mkFreshIdent name
  let thmCmd <- `(command|
  @[loomSpec, loomWpSimp]
  noncomputable
  def $wp_name $args_list:bracketedBinder* : WPGen ($name : $m $out) := by
    econstructor; intro post
    have : $name = liftM (n := $m) ($name : $type) := by rfl
    rewrite [this]
    rewrite [MAlgLift.wp_lift]
    simp only [loomLogicLiftSimp]
    simp only [loomWPGenRewrite]
    rfl)
  trace[Loom] m!"{thmCmd}"
  elabCommand thmCmd

elab "#derive_wp" args:explicitBinders ? "for" "(" name:term ":" type:term ")" : command => do
  let args_list ← liftTermElabM do
    match args with
    | .some args => do
      toBracketedBinderArray args
    | .none => pure #[]
  let wp_name ← mkFreshIdent name
  let thmCmd <- `(command|
  @[loomSpec, loomWpSimp]
  noncomputable
  def $wp_name $args_list:bracketedBinder* : WPGen ($name : $type) := by
    econstructor; intro post
    simp only [loomWPGenRewrite]
    rfl)
  trace[Loom] m!"{thmCmd}"
  elabCommand thmCmd
