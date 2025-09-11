import Lean
import Loom.MonadAlgebras.WP.Gen

open Lean Meta Elab Term

namespace Loom.Matcher

theorem simp1 {l : Type u} [CompleteBooleanAlgebra l] {p : Prop} (proof : p) {a b : l} (h : a ≤ b) :
  ⌜p⌝ ⇨ a ≤ b := by simp [proof] ; exact h

theorem simp2 {l : Type u} {α : Sort v} [CompleteBooleanAlgebra l] {a b : l} {c : α} (h : a ≤ b) :
  ⌜c = c⌝ ⇨ a ≤ b := by simp ; exact h

/-- Given `e` as the `Expr` of `∀ (x₁ : t₁) ⋯ (xₙ : tₙ), ⋯`, this returns
    `[(x₁, Expr(t₁), bi₁), ⋯, (xₙ, Expr(tₙ), biₙ)]`, where `biᵢ` is the `BinderInfo` of `xᵢ`. -/
private def getForallPremises : Expr → List (Name × Expr × BinderInfo)
  | .forallE na ty body bi =>
    (na, ty, bi) :: getForallPremises body
  | _ => []

private def List.foldldM.{u, v, w} {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} (f : s → α → m s)
  (g : α → m s) (init : s) (l : List α) : m s :=
  match l with
  | [] => pure init
  | a :: l' => do
    let init' ← g a
    List.foldlM f init' l'

def WPGen.match_template.{u, v} {m : Type u → Type v} [Monad m] [LawfulMonad m]
  {l : Type u} [CompleteBooleanAlgebra l] [MAlgOrdered m l] := Unit.unit

private partial def withinBranch (i n : Nat) (type mainGoal : Expr) : TermElabM Expr := do
  if n <= 1 then return mainGoal
  -- let mv ← mkFreshExprMVar type
  -- let outerProof left? pf := mkAppOptM (if left? then ``inf_le_of_left_le else ``inf_le_of_right_le)
  --   #[.some type, .none, (if left? then .none else .some mv), (if left? then .some mv else .none), .none, .some pf]
  -- let goal ← mkFreshExprMVar none
  if i = n - 1 then
    -- let tmp ← outerProof false goal
    let tmp ← mainGoal.mvarId!.applyConst ``inf_le_of_right_le
    -- let _ ← isDefEq mainGoal tmp
    return .mvar tmp[0]!
  -- let tmp ← outerProof true goal
  -- let _ ← isDefEq mainGoal tmp
  -- withinBranch i (n - 1) type goal
  let tmp ← mainGoal.mvarId!.applyConst ``inf_le_of_left_le
  -- let _ ← isDefEq mainGoal tmp
  withinBranch i (n - 1) type <| .mvar tmp[0]!

/-
Only consider the case where each match alternative is a monadic computation `m α`.

How will the arguments of a matcher's `WPGen` look like?
- Consider the matcher itself. When we set `motive` to `fun _ => m α`, then each argument
  corresponds to the monadic computations for which we need to construct `WPGen`s
  as subgoals.
- From the types of those arguments, we can figure out the types of the `WPGen` subgoals.
- Now consider its `splitter`. Each argument of the `splitter` corresponds to one
  "branch" of the `WPGen.get`; "branches" are connected by `⊓` (in analogy to `∧`).
  In one "branch", we have a series of `⨅ ..., ⌜ ... ⌝ ⇨ ...` (in analogy to `∀ ..., ... → ...`).
  The `⌜ ... ⌝`'s consist of the inner arguments of each argument of the `splitter`
  and also equalities on the discriminant(s) of the `match`.
- Proving `WPGen.prop` with regard to this `WPGen.get` is relatively straightforward.

Store the generated `WPGen` element for a certain matcher since it might be used later.

-/

/-- Construct a suitable `WPGen` term for a matcher in real time. -/
def constructWPGen (matcherName : Name) : TermElabM (Option (Array Name × Expr)) := do
  -- NOTE: we rely on `MatcherInfo` here, since we do not want to generate
  -- `WPGen` only for a specific matcher; but this might not work on `casesOn`.
  -- in that case, we might rely on `MatcherApp` instead
  let some matcherInfo ← getMatcherInfo? matcherName | return none
  let constInfo ← getConstInfo matcherName
  -- use level mvars to be more flexible
  let lvlMVars ← mkFreshLevelMVars constInfo.levelParams.length

  -- make up the discriminant(s) and related (type) parameter(s)
  -- NOTE: this will also introduce a fvar for `motive`, but we do not use it TODO really?
  forallBoundedTelescope (constInfo.type.instantiateLevelParams constInfo.levelParams lvlMVars) (.some matcherInfo.getFirstAltPos) fun paramsAndDiscrs partialMatcher => do
  let discrs := paramsAndDiscrs.drop matcherInfo.getFirstDiscrPos |>.take matcherInfo.numDiscrs

  -- make up the implicit arguments of this `WPGen`
  forallTelescope (← ConstantInfo.type <$> getConstInfo ``WPGen.match_template) fun implicitArgs _ => do
  let (mExpr, monadInstExpr, lExpr, omaInstExpr) := (implicitArgs[0]!, implicitArgs[1]!, implicitArgs[3]!, implicitArgs[5]!)

  -- `α`: make up the return type of `m`
  withLocalDecl (← mkFreshUserName `α) BinderInfo.implicit (← Expr.bindingDomain! <$> inferType mExpr) fun αExpr => do

  -- make up the monadic computations in alternatives
  let wpgenTypeBuilder x : MetaM Expr :=
    -- for convenience, here leave some arguments to be resolved by typeclass resolution
    mkAppOptM ``WPGen #[.some mExpr, .some monadInstExpr, .some αExpr, .some lExpr, .none, .some omaInstExpr, .some x]
  /-
  TODO better abstraction? over `motivefv`, `input`
  let subMonadArgs ← metaBetaReduceForMotive (fun _ => mkApp mExpr αExpr) splitterType app
  -/
  let motivefv := paramsAndDiscrs[matcherInfo.getMotivePos]!
  let branchConds ← do
    pure <| List.map (fun x => (x.1, x.2.1)) <| getForallPremises partialMatcher
  let subMonadArgs ← branchConds.mapM fun (nm, br) => do
    let tmp ← Core.transform br
      (pre := fun e => pure <| e.withApp (fun f args =>
        if f == motivefv
        then .done <| mkApp mExpr αExpr
        else .continue))
    pure (nm, tmp)
  trace[Loom.debug] "subMonadArgs: {subMonadArgs}"
  withLocalDecls (← subMonadArgs.toArray.mapM fun (nm, t) => do
      let nm' ← mkFreshUserName nm
      pure (nm', BinderInfo.implicit, fun _ => pure t)) fun subMonadArgsFVars => do

  -- make up the sub `WPGen` goals
  let subWPGenArgs ← subMonadArgs.mapIdxM fun i (nm, t) => do
    let nm' := nm.appendBefore "wpg"
    let ty ← forallTelescope t fun xs _ => do
      let tmp := mkAppN subMonadArgsFVars[i]! xs
      let tmp ← wpgenTypeBuilder tmp
      mkForallFVars xs tmp
    pure (nm', ty)
  trace[Loom.debug] "subWPGenArgs: {subWPGenArgs}"
  -- TODO repeating code
  withLocalDecls (← subWPGenArgs.toArray.mapM fun (nm, t) => do
      let nm' ← mkFreshUserName nm
      pure (nm', BinderInfo.implicit, fun _ => pure t)) fun subWPGenArgsFVars => do

  -- make up the type of the target `WPGen`
  let targetMatcher ← do
    let motivefv := paramsAndDiscrs[matcherInfo.getMotivePos]!
    let ty ← inferType motivefv
    let motiveArg ← forallTelescope ty fun xs _ =>
      mkLambdaFVars xs <| mkApp mExpr αExpr
    pure <| mkAppN
      (Lean.mkConst matcherName lvlMVars)
      ((paramsAndDiscrs.set! matcherInfo.getMotivePos motiveArg) ++ subMonadArgsFVars)
  let targetWPGenTy ← wpgenTypeBuilder targetMatcher
  trace[Loom.debug] "targetWPGenTy: {targetWPGenTy}"

  -- prepare the splitter
  let (splitter, splitterType) ← do
    let matchEqns ← Match.getEquationsFor matcherName
    -- note the difference on instantiating level params
    let splitter ← mkConstWithFreshMVarLevels matchEqns.splitterName
    let splitterType ← whnfForall (← inferType <| Lean.mkConst matchEqns.splitterName lvlMVars)
    pure (splitter, splitterType)
  trace[Loom.debug] "splitter type: {splitterType}"

  -- make up the `post`
  withLocalDeclD (← mkFreshUserName `post) (← mkArrow αExpr lExpr) fun postExpr => do

  -- make up the `WPGen.get`
  -- CHECK `backup` might include unnecessary information
  let (wpgenGet, backup) ← do
    -- let fakeMotiveFv := Expr.fvar (← mkFreshFVarId)
    -- the `motive` is fake here
    let partialSplitterType ← instantiateForall splitterType paramsAndDiscrs -- (paramsAndDiscrs.set! matcherInfo.getMotivePos fakeMotiveFv)
    let branchConds ← do
      pure <| List.map (fun x => x.2.1) <| getForallPremises partialSplitterType
    let wpgenGetBranches ← branchConds.mapIdxM fun i br => do
      let subWPGen := subWPGenArgsFVars[i]!
      let br' ← forallTelescope br fun xs motiveBody => do
        -- TODO for `Unit → ...`, this will not work; fix it later
        let newBody ← do
          let numArgsRequired ← Expr.getNumHeadForalls <$> inferType subWPGen
          let subWPGenGet ← mkAppM ``WPGen.get #[mkAppN subWPGen (xs.take numArgsRequired), postExpr]
          motiveBody.withApp fun _ args => do
            -- TODO this should have an optimization; some equalities might be redundant
            let eqs ← discrs.mapIdxM fun i lhs => mkEq lhs args[i]!
            mkArrowN eqs subWPGenGet
        mkForallFVars xs newBody
      trace[Loom.debug] "branch {i} after adding equalities: {br} ==> {br'}"
      let res ← forallTelescope br' fun xs motiveBody' => do
        xs.foldrM (init := motiveBody') fun x e => do
          let xty ← inferType x
          if ← isProp xty then
            let injectedProp ← mkAppOptM ``LE.pure #[.some lExpr, .none, .none, .none, .some xty]
            mkAppOptM ``himp #[.some lExpr, .none, .some injectedProp, .some e]
          else
            let tmp ← mkLambdaFVars #[x] e
            mkAppOptM ``iInf #[.some lExpr, .some xty, .none, .some tmp]
      trace[Loom.debug] "branch {i} after transformation: {br'} ==> {res}"
      pure (br', res)
    let (wpgenGetBranchesBefore, wpgenGetBranchesAfter) := wpgenGetBranches.unzip
    -- combine the branches together; `⊓` is left-associative
    -- NOTE: this might also be changed into another encoding, e.g., `⨅ i ∈ (Fin ..), ...`
    let topAsInit ← mkAppOptM ``Top.top #[.some lExpr, .none]
    let bundled ← List.foldldM (g := pure) (init := topAsInit) (l := wpgenGetBranchesAfter) fun infs e =>
      mkAppOptM ``Min.min #[.some lExpr, .none, .some infs, .some e]
    let res ← mkLambdaFVars #[postExpr] bundled
    pure (res, wpgenGetBranchesBefore.toArray)
  trace[Loom.debug] "wpgenGet: {wpgenGet}"

  -- make up the proof for `WPGen.post`
  -- NOTE: this proof might also be done using tactics
  let wpgenPost ← do
    let motive ← do
      let lhs ← instantiateLambda wpgenGet #[postExpr]
      let rhs ← mkAppOptM ``wp
        #[.some mExpr, .some monadInstExpr, .some αExpr, .some lExpr, .none,
          .some omaInstExpr, .some targetMatcher, .some postExpr]
      let le ← mkAppM ``LE.le #[lhs, rhs]
      mkLambdaFVars discrs le
    trace[Loom.debug] "motive for the splitter in proof: {motive}"
    let paramsAndDiscrs' := paramsAndDiscrs.set! matcherInfo.getMotivePos motive
    let partialSplitter := mkAppN splitter paramsAndDiscrs'
    let partialSplitterType ← inferType partialSplitter
    let numBranches := matcherInfo.numAlts    -- should be the same as `branchConds.length`
    let branchConds ← do
      pure <| List.map (fun x => x.2.1) <| List.take numBranches <| getForallPremises partialSplitterType
    let wpgenPostSubProofs ← branchConds.toArray.mapIdxM fun i br => do
      trace[Loom.debug] "subgoal {i}: {br}"
      -- `intro`
      let res ← forallTelescope br fun xs body => do
        -- instantiate the sub `WPGen` to use
        let subWPGen := subWPGenArgsFVars[i]!
        -- TODO maybe store this information ahead of recomputing since it is used twice
        let numArgsRequired ← Expr.getNumHeadForalls <$> inferType subWPGen
        let subWPGenProp ← mkAppM ``WPGen.prop #[mkAppN subWPGen (xs.take numArgsRequired), postExpr]
        -- build the proof by looking at the corresponding branch of `wpgenGet`

        let goal ← mkFreshExprMVar body

        let goal_ ← withinBranch i numBranches lExpr goal

        -- do the prefix part
        let goal' ← xs.foldlM (init := goal_) fun mainGoal x => do
          let xty ← inferType x
          trace[Loom.debug] "xty: {xty}"
          if ← isProp xty then
            -- let goal' ← mkFreshExprMVar none
            -- let tmp ← mkAppOptM ``Loom.Matcher.simp1 #[.some lExpr, .none, .none, .none, .none, .some x, .some goal']
            -- let _ ← isDefEq mainGoal tmp
            -- pure goal'
            let tmp ← mkAppOptM ``Loom.Matcher.simp1 #[.some lExpr, .none, .some xty, .some x]
            let goals ← mainGoal.mvarId!.apply tmp
            pure <| .mvar goals[0]!
          else
            -- need to provide the function?
            -- let ety ← inferType e
            -- trace[Loom.debug] "ety: {ety}"
            -- let tmp ← match_expr ety with
            --   | LE.le _ _ lhs _ =>
            --     -- let nm ← x.fvarId!.getUserName
            --     -- pure <| some <| Expr.lam nm xty lhs BinderInfo.default
            --     mkLambdaFVars #[x] lhs
            --   | _ => pure none

            -- let goal' ← mkFreshExprMVar none
            -- let tmp ← mkAppOptM ``iInf_le_of_le #[.some lExpr, .some xty, .none, .none /- ! -/ , .none, .some x, .some goal']
            -- let _ ← isDefEq mainGoal tmp
            -- pure goal'
            let f ← mkFreshExprMVar (← mkArrow xty lExpr)
            let a ← mkFreshExprMVar lExpr
            let tmp ← mkAppOptM ``iInf_le_of_le #[.some lExpr, .some xty, .none, .some f /- ! -/ , .some a, .some x]
            let goals ← mainGoal.mvarId!.apply tmp
            pure <| .mvar goals[0]!

        -- try `rfl` in the trailing part
        let n := backup[i]!.getNumHeadForalls
        let goal'' ← (n - xs.size) |>.foldM (init := goal') fun _ _ mainGoal => do
          -- let mv ← mkFreshExprMVar .none
          -- let rfl ← mkEqRefl mv
          -- let goal' ← mkFreshExprMVar none
          -- let tmp ← mkAppOptM ``Loom.Matcher.simp1 #[.some lExpr, .none, .none, .none, .none, .some rfl, .some goal']
          -- let _ ← isDefEq mainGoal tmp
          -- pure goal'
          let goals ← mainGoal.mvarId!.applyConst ``Loom.Matcher.simp2
          pure <| .mvar goals[0]!
        let _ ← isDefEq subWPGenProp goal''

/-
        -- try `rfl` in the trailing part
        let n := backup[i]!.getNumHeadForalls
        let rflProof ← (n - xs.size) |>.foldM (init := subWPGenProp) fun _ _ e => do
          let mv ← mkFreshExprMVar .none
          let rfl ← mkEqRefl mv
          mkAppOptM ``Loom.Matcher.simp1 #[.some lExpr, .none, .none, .none, .none, .some rfl, .some e]
        trace[Loom.debug] "rflProof: {rflProof}"
        -- do the prefix part
        let proof ← xs.foldrM (init := rflProof) fun x e => do
          let xty ← inferType x
          trace[Loom.debug] "xty: {xty}"
          if ← isProp xty then
            mkAppOptM ``Loom.Matcher.simp1 #[.some lExpr, .none, .none, .none, .none, .some x, .some e]
          else
            -- need to provide the function?
            let ety ← inferType e
            trace[Loom.debug] "ety: {ety}"
            let tmp ← match_expr ety with
              | LE.le _ _ lhs _ =>
                -- let nm ← x.fvarId!.getUserName
                -- pure <| some <| Expr.lam nm xty lhs BinderInfo.default
                mkLambdaFVars #[x] lhs
              | _ => pure none
            mkAppOptM ``iInf_le_of_le #[.some lExpr, .some xty, .none, tmp, .none, .some x, .some e]
        -- do the branch selection
        let res ← withinBranch i numBranches lExpr proof
-/
        let res ← instantiateMVars goal
        mkLambdaFVars xs res
      trace[Loom.debug] "sub-proof for branch {i}: {br} ==> {res}"
      pure res
    mkLambdaFVars #[postExpr] <| mkAppN partialSplitter wpgenPostSubProofs

  -- put together
  let wpgen ← mkAppM ``WPGen.mk #[wpgenGet, wpgenPost]
  check wpgen
  let wpgen ← instantiateMVars wpgen
  let arguments :=
    #[αExpr] ++
    (paramsAndDiscrs.take matcherInfo.numParams) ++
    implicitArgs ++
    subMonadArgsFVars ++
    subWPGenArgsFVars ++
    (paramsAndDiscrs.drop matcherInfo.getFirstDiscrPos)
  let wpgen ← mkLambdaFVars arguments wpgen
  trace[Loom.debug] "generated WPGen: {wpgen}"
  trace[Loom.debug] "has mvar? {wpgen.hasMVar}"

  -- NOTE: it seems that only this requires `TermElabM`; the rest can be done in `MetaM`
  let wpgen ← levelMVarToParam wpgen
  trace[Loom.debug] "has mvar? {wpgen.hasMVar}"
  let newLvls := collectLevelParams {} wpgen |>.params
  -- Option.some <$>
  pure (newLvls, wpgen)

def defineWPGen (name : Name) : TermElabM Unit := do
  unless ← isMatcher name do
    throwError s!"{name} is not a matcher"
  let targetName := name ++ `WPGen
  if (← getEnv).find? targetName matches none then
    let some (newLvls, wpgen) ← constructWPGen name
      | throwError s!"cannot generate WPGen for matcher {name} due to error"
    addDecl <|
      Declaration.defnDecl <|
        mkDefinitionValEx targetName newLvls.toList (← inferType wpgen) wpgen
        (Lean.ReducibilityHints.regular 0)
        (DefinitionSafety.safe) []
    enableRealizationsForConst targetName
    applyAttributes targetName (← do
      let attr1 ← `(Parser.Term.attrInstance| spec )
      let attr2 ← `(Parser.Term.attrInstance| loomWpSimp)
      elabAttrs #[attr1, attr2])

-- inspired by how `.fun_cases` works
def isMatcherWPGen (env : Environment) (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  unless isMatcherCore env p do return false
  match s with
  | "WPGen" =>
    unless env.isSafeDefinition p do return false
    return true
  | _ => return false

end Loom.Matcher

-- FIXME: does not seem to actually work. why?
-- initialize
--   registerReservedNamePredicate Loom.Matcher.isMatcherWPGen

--   registerReservedNameAction fun name => do
--     if Loom.Matcher.isMatcherWPGen (← getEnv) name then
--       let .str p _ := name | return false
--       unless (← getEnv).isSafeDefinition p do return false
--       MetaM.run' <| realizeConst p name (Loom.Matcher.defineWPGen p |>.run')
--       return true
--     return false
