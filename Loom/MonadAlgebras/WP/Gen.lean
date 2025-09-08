import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import Loom.MonadAlgebras.WP.Basic
import Loom.MonadAlgebras.WP.Liberal
import Loom.MonadAlgebras.WP.DoNames'

open Lean Meta Elab Command Term

universe u v w

private def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimpleScopedEnvExtension.modify
  (ext : SimpleScopedEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

private def _root_.Lean.SimplePersistentEnvExtension.get [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimplePersistentEnvExtension.modify
  (ext : SimplePersistentEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

structure LoomAssertionsMap where
  maxId : Int
  syntaxStore : Std.HashMap Int Term
  nameStore : Std.HashMap Name Int
  nameCounter : Std.HashMap Name Int

  deriving Inhabited

def addAssertion (s : LoomAssertionsMap) (t : Term) (n : Name) (coreName: Name): LoomAssertionsMap :=
  let maxId := s.maxId + 1
  let maxIdLocal := s.nameCounter.get! coreName + 1
  { s with
    maxId := maxId
    syntaxStore := s.syntaxStore.insert maxId t
    nameStore := s.nameStore.insert n maxId
    nameCounter := s.nameCounter.insert coreName maxIdLocal }

initialize loomAssertionsMap :
  SimplePersistentEnvExtension (Term × Name × Name) LoomAssertionsMap <-
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s ⟨t, n, coreName⟩ => addAssertion s t n coreName
    addImportedFn := fun as => Id.run do
      let mut res : LoomAssertionsMap := default
      for a in as do
        for (t, n, coreName) in a do
          res := addAssertion res t n coreName
      return res
  }

section
variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u} [CompleteLattice l] [MAlgOrdered m l]

set_option linter.unusedVariables false in
def invariantGadget {invType : Type u} (inv : List invType): m PUnit := pure .unit

@[simp]
abbrev invariants (f : List l) := f.foldr (·⊓·) ⊤

-- macro "invariant" t:term : invariantClause => `(invariantGadget $t)


set_option linter.unusedVariables false in
def onDoneGadget {invType : Type u} (inv : invType) : m PUnit := pure .unit


set_option linter.unusedVariables false in
def assertGadget {l : Type u} (h : l) : m PUnit := pure .unit


set_option linter.unusedVariables false in
def decreasingGadget (measure : ℕ) : m PUnit := pure .unit

elab "with_name_prefix" lit:name inv:term : term => do
  let ⟨maxId, _, _, cntr⟩ <- loomAssertionsMap.get
  let newMaxId := maxId + 1
  let coreName := match (← Term.getDeclName?) with
    | some res => res
    | none => `nameless
  let localName := (Lean.Name.mkSimple (lit.getName.toString ++ "_" ++ coreName.toString))
  let cntrElem := match cntr.get? localName with
    | some resId => resId
    | none => 0
  let maxIdLocal := 1 + cntrElem
  let invName := lit.getName.toString ++ "_" ++ toString maxIdLocal.toNat |>.toName
  loomAssertionsMap.modify (fun res => {
      syntaxStore := res.syntaxStore.insert newMaxId inv
      nameStore := res.nameStore.insert invName newMaxId
      maxId := newMaxId
      nameCounter := res.nameCounter.insert localName maxIdLocal
      })
  Term.elabTerm (<- ``(WithName $inv $(Lean.quoteNameMk invName))) none

elab "type_with_name_prefix" lit:name inv:term : term => do
  let ⟨maxId, _, _, cntr⟩ <- loomAssertionsMap.get
  let newMaxId := maxId + 1
  let coreName := match (← Term.getDeclName?) with
    | some res => res
    | none => `nameless
  let localName := (Lean.Name.mkSimple (lit.getName.toString ++ "_" ++ coreName.toString))
  let cntrElem := match cntr.get? localName with
    | some resId => resId
    | none => 0
  let maxIdLocal := 1 + cntrElem
  let invName := lit.getName.toString ++ "_" ++ toString maxIdLocal.toNat |>.toName
  loomAssertionsMap.modify (fun res => {
      syntaxStore := res.syntaxStore.insert newMaxId inv
      nameStore := res.nameStore.insert invName newMaxId
      maxId := newMaxId
      nameCounter := res.nameCounter.insert localName maxIdLocal
      })
  Term.elabTerm (<- ``(typeWithName $inv $(Lean.quoteNameMk invName))) none


def termBeforeInvariant := Parser.withForbidden "invariant" Parser.termParser

attribute [run_builtin_parser_attribute_hooks] termBeforeInvariant

builtin_initialize
  register_parser_alias termBeforeInvariant

structure WPGen (x : m α) where
  get : Cont l α
  -- sideCond : l := ⊤
  prop : ∀ post, get post <= wp x post

omit [LawfulMonad m] in
lemma WPGen.intro (x : m α) (wpg : WPGen x) :
  pre <= wpg.get post ->
  -- pre <= wpg.sideCond ->
  triple pre x post := by
  intro h; apply le_trans'; apply wpg.prop; apply_assumption

def WPGen.default (x : m α) : WPGen x where
  get := wp x
  prop := by intro post; simp

def WPGen.pure (x : α) : WPGen (pure (f := m) x) where
  get := fun post => post x
  prop := by intro post; simp [wp_pure]

def WPGen.bind {x : m α} {f : α -> m β} (wpg : WPGen x) (wpgf : ∀ a, WPGen (f a)) :
  WPGen (x >>= f) where
  get := fun post => wpg.get (fun a => (wpgf a).get post)
  prop := by
    intro post; simp [wp_bind]; apply le_trans
    apply wpg.prop; apply wp_cons; intro a; apply (wpgf a).prop

def WPGen.map {x : m α} {f : α -> β} (wpg : WPGen x) : WPGen (f <$> x) where
  get := fun post => wpg.get (fun a => post (f a))
  prop := by
    rw [map_eq_pure_bind]; simp only [wp_bind, wp_pure]; intro
    apply le_trans; solve_by_elim [wpg.prop]; rfl

noncomputable
def WPGen.spec_triple (x : m α) (trp : triple pre x post) : WPGen x where
  get := spec pre post
  prop := by rw [<-triple_spec] at trp; solve_by_elim

-- noncomputable
-- def WPGen.spec_triple_invs (x : m α) (trp : invs -> triple pre x post) : WPGen x where
--   get := spec pre post
--   prop := by rw [<-triple_spec] at trp; solve_by_elim

def WPGen.spec_wp wp' (x : m α) (trp : wp x = wp') : WPGen x where
  get := wp'
  prop := by
    intro post
    subst trp
    simp

theorem triple_forIn_deacreasing {β} {measure : β -> ℕ}
  {init : β} {f : β → m (ForInStep β)}
  (inv : β → l)
  (hstep : ∀ b,
    measure b <= measure init ->
    triple
      (inv b)
      (f b)
      (fun | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝ | .done b' => ⌜ measure b' = 0 ⌝ ⊓ inv b')) :
  triple (inv init) (forIn [0:measure init] init (fun _ => f)) (fun b => inv b ⊓ ⌜measure b = 0⌝) := by
  apply le_trans'; apply wp_cons; rotate_left 2; apply le_trans; rotate_left 1
  apply triple_forIn_range_step1 (inv := fun i b => ⌜ measure b + i <= measure init ⌝ ⊓ inv b) <;>
    try solve | aesop
  { simp; intro i b
    by_cases h : measure b + i ≤ measure init <;> simp [h, triple]
    apply le_trans; apply hstep; omega
    apply wp_cons; rintro (b'|b') <;> simp
    by_cases h: measure b' = 0 <;> simp [h]
    by_cases h': measure b' < measure b <;> simp [h']
    have : measure b' + (i + 1) ≤ measure init := by omega
    simp [this] }
  { simp; intro b
    by_cases h : measure b + measure init ≤ measure init <;> simp [h]
    by_cases h' : measure b = 0 <;> simp [h']
    omega }
  simp

attribute [-simp] Std.Range.forIn_eq_forIn_range' in
noncomputable
def WPGen.forWithInvariant {xs : Std.Range} {init : β} {f : ℕ → β → m (ForInStep β)}
  (inv : ℕ → β → List l) (wpg : ∀ i b, WPGen (f i b)) (xs1 : xs.step = 1) (xs_le : xs.start <= xs.stop := by omega) :
    WPGen (forIn xs init (fun i b => do invariantGadget (inv i b); (f i b))) where
    get := ⌜∀ i b, invariants (inv i b) <= (wpg i b).get fun
      | .yield b' => invariants <| inv (i + 1) b'
      | .done b'  => invariants <| inv xs.stop b'⌝
      ⊓ spec
      ((inv xs.start init).foldr (·⊓·) ⊤)
      (fun b => (inv xs.stop b).foldr (·⊓·) ⊤)
    prop := by
      intro post; simp only [LE.pure]; split_ifs with h <;> try simp
      apply (triple_spec ..).mpr
      simp [invariantGadget]
      apply triple_forIn_range_step1 (fun i b => (inv i b).foldr (·⊓·) ⊤)
      simp [invariants, <-xs1] at h
      intro i b; apply (wpg i b).intro
      all_goals solve_by_elim

-- noncomputable
-- def WPGen.forWithInvariantDecreasing {β} {measure : β -> ℕ}
--   {init : β} {f : β → m (ForInStep β)}
--   (inv : β → List l) :
--     WPGen (forIn [0:mb] init (fun _ b => do decreasingGadget (measure b); invariantGadget (inv b); f b)) := by
--   apply spec_triple_invs (invs :=
--     mb = measure init ∧
--     (∀ b, measure b <= measure init -> triple (invariants (inv b)) (f b) (fun | .yield b' => invariants (inv b') ⊓ ⌜measure b' < measure b⌝ | .done b' => ⌜ measure b' = 0 ⌝ ⊓ invariants (inv b'))))
--   simp only [and_imp]; intros eq h; simp only [eq]
--   apply triple_forIn_deacreasing (fun b => invariants (inv b)); simp [invariantGadget, decreasingGadget]
--   solve_by_elim

end
variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u} [CompleteBooleanAlgebra l] [MAlgOrdered m l]


def WPGen.assert {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MAlgOrdered m l] (h : l) : WPGen (assertGadget (m := m) h) where
  get := fun post => h ⊓ (h ⇨ post .unit)
  prop := by simp [assertGadget, wp_pure]

noncomputable
def WPGen.if {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MAlgOrdered m l]
  {hd : Decidable h} {x y : m α}
  (wpgx : h → WPGen x) (wpgy : ¬h → WPGen y)
  : WPGen (if h then x else y) where
  get := fun post =>
    (⨅ hc : WithName h (Lean.Name.anonymous.mkStr "if_pos"), (wpgx hc).get post) ⊓
    (⨅ hc : WithName (¬h) (Lean.Name.anonymous.mkStr "if_neg"), (wpgy hc).get post)
  prop := by
    intro post
    split
    { refine inf_le_of_left_le ?_
      apply iInf_le_iff.mpr
      rename_i hc
      intro b hi
      apply le_trans (b := (wpgx hc).get post)
      exact hi hc
      apply (wpgx hc).prop }
    refine inf_le_of_right_le ?_
    apply iInf_le_iff.mpr
    rename_i hc
    intro b hi
    apply le_trans (b := (wpgy hc).get post)
    exact hi hc
    apply (wpgy hc).prop

noncomputable
def WPGen.let  {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MAlgOrdered m l]
  (y : β) {x : β -> m α} (wpgx : ∀ y, WPGen (x y)) : WPGen (let z := y; x z) where
  get := fun post => ⨅ z, ⌜z = y⌝ ⇨ (wpgx z).get post
  prop := by
     intro post; simp; refine iInf_le_of_le y ?_
     simp; apply (wpgx y).prop


noncomputable
def WPGen.match
  {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MAlgOrdered m l]
  -- The program to run if the option is 'none'
  {y : m β} {z : γ  → m β} (opt : Option γ ) (wpgy : WPGen y)
  -- A function that gives a program to run if the option is 'some a'
  (wpgz : ∀ a, WPGen (z a)) 
  -- The return type is parameterized by the whole match expression
  : WPGen (match opt with | none => y | some a => z a)
where
  get := fun post =>
    -- Branch 1: The 'none' case
    (⌜opt = none⌝ ⇨ wpgy.get post) ⊓
    -- Branch 2: The 'some' case
    (⨅ a, ⌜opt = some a⌝ ⇨ (wpgz a).get post)

  prop := by
    intro post; simp [LE.pure]
    -- The proof strategy is to analyze the value of 'opt'
    cases opt with
    | none =>
      -- If opt is none, the formula simplifies to the precondition for y
      simp [wpgy.prop]
    | some a =>
      -- If opt is some a, the formula simplifies to the precondition for z a
      simp [(wpgz a).prop]
      refine iInf_le_of_le ?_ ?_ 
      · assumption
      · simp
        exact (wpgz a).prop post


syntax (name:=generate_predicates) "#generate_predicates" ident : command

@[command_elab generate_predicates ]
def generate_predicates_impl: CommandElab := fun stx => do
  match stx with
  | `(command| #generate_predicates $typeName:ident) =>
    let fullName ← resolveGlobalConstNoOverload typeName
    let info ← getConstInfoInduct fullName
    let inductiveTypeName := info.name
    let mut generatedCmds := #[]
    for ctorName in info.ctors do
      let ctorInfo <- getConstInfoCtor ctorName
      let arity := ctorInfo.numFields
      let placeholders := Array.replicate arity (← `(_))
      let ctorShortName := ctorName.lastComponentAsString 
      let funName := mkIdent $ Name.mkStr 
                (Name.mkStr Name.anonymous inductiveTypeName.lastComponentAsString ) 
                ("is" ++ ctorShortName.capitalize )
      let ctor := mkIdent ctorName
      let typeIdent := mkIdent typeName.getId
      let cmd ← `(command|
        @[simp]
        def $funName:ident (c : $typeIdent:ident) : Bool :=
          match c with
          | $ctor:ident $placeholders:term*  => true
          | _     => false
      )
      generatedCmds := generatedCmds.push cmd
    let finalSyntax := mkNullNode generatedCmds
    elabCommand finalSyntax
  | _ => throwUnsupportedSyntax


syntax (name:=generate_immediate_structures) "#generate_immediate_structures" ident : command

@[command_elab generate_immediate_structures ]
def generate_immediate_structures_impl: CommandElab := fun stx => do
  match stx with
  | `(command| #generate_immediate_structures $typeName:ident) =>
    let fullName ← resolveGlobalConstNoOverload typeName
    let info ← getConstInfoInduct fullName
    let inductiveTypeName := info.name
    let mut generatedCmds := #[]
    for ctorName in info.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorShortName := ctorName.lastComponentAsString 
      -- Define the new structure's name, e.g., "Rect" -> "RectFields"
      let structName := mkIdent $ Name.mkStr 
                  (Name.mkStr Name.anonymous inductiveTypeName.lastComponentAsString ) 
                  (ctorShortName.capitalize ++ "Fields")

      let cmd ← liftTermElabM $ forallTelescope ctorInfo.type fun fields _ => do

        let mut paramBinders := #[]
        for param in fields do
          let decl ← getFVarLocalDecl param
          let paramName := mkIdent decl.userName
          let paramTypeSyntax ← withOptions (fun o => o.setBool `pp.universes true) do Lean.PrettyPrinter.delab decl.type
          logInfo paramName
          logInfo paramTypeSyntax
          paramBinders := paramBinders.push (← `(bracketedBinder| ($paramName : $paramTypeSyntax)))

        logInfo fields

        let ctorFields := fields.extract ctorInfo.numParams fields.size
        -- This is the new array for our correctly parsed field binders
        let mut fieldBinders := #[]
        /- let mut typeParams := #[] -/
        for field in ctorFields do
          logInfo field
          let decl ← getFVarLocalDecl! field
          let fieldName := mkIdent decl.userName
          logInfo fieldName
          let inferredType <- inferType field
          logInfo s!"{inferredType} , is mVar:{inferredType.isMVar}, isFVar: {inferredType.isFVar}, name: {inferredType.constName?}"
          let fieldType ← withOptions (fun opts =>
                opts.setBool `pp.implicits true |>.setBool `pp.universes false
              ) do
                -- Use the MetaM-native delab that you found!
                Lean.PrettyPrinter.delab inferredType
          /- let fieldType <- Lean.PrettyPrinter.delab  inferredType -/
          logInfo fieldType
          let binder := `(Lean.Parser.Command.structSimpleBinder|$fieldName:ident : $fieldType)
          fieldBinders := fieldBinders.push (← binder)

        let structFields <- `(Lean.Parser.Command.structFields| $fieldBinders* )
        logInfo structName

        `(command|
          @[ext]
          structure $structName:ident $paramBinders:bracketedBinder* where
            make:: 
            $structFields
          )

      generatedCmds := generatedCmds.push cmd
    let finalSyntax := mkNullNode generatedCmds
    elabCommand finalSyntax
  | _ => throwUnsupportedSyntax

-- Our test type
inductive Vehicle where
  | car (make : String) (year : Nat)
  | bike (hasBell : Bool)
  | unicycle

#check Vehicle.rec
#generate_predicates Vehicle
#generate_immediate_structures Vehicle
#print Vehicle.CarFields

set_option pp.rawOnError true
#generate_predicates Nat
#generate_immediate_structures Option
#print Option.SomeFields


set_option trace.Meta.Tactic.simp true

simproc reduceWPGenMatch (WPGen _) :=
  fun e => do
    let args := e.getAppArgs
    if h: args.size = 0 then return .done {expr:= e}
    else 
      let match_exp := args[args.size - 1 ]!
      let univ_levels :=  e.getAppFn.constLevels!
      dbg_trace "Match Expression: {match_exp}"
      if let some e' := (← Lean.Meta.matchMatcherApp? match_exp) then
        let res <- Lean.Meta.MatcherApp.transform (onAlt := (fun a b e => do
          -- all args but last one replaced
          let args' := args.set (args.size - 1) e (by 
            grind
          )
          /- let args' := #[e] -/
          let newExpr := (mkAppN (Lean.Expr.const ``WPGen univ_levels)  args' )
          dbg_trace "e1: {b}, e2: {e}"
          dbg_trace "Transformed from {e} -> {newExpr}" 
          pure newExpr
        )) (onMotive:= (fun _ e => do
          dbg_trace "Motive: {e}"
          pure e
        )) e'
        dbg_trace "{res.toExpr}"
        return .done { expr := res.toExpr }
      else 
        return .done { expr := e }
