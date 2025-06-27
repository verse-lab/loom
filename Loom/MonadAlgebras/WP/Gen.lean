import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import Loom.MonadAlgebras.WP.Basic
import Loom.MonadAlgebras.WP.Liberal
import Loom.MonadAlgebras.WP.DoNames'

open Lean Elab Command

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

  deriving Inhabited

def addAssertion (s : LoomAssertionsMap) (t : Term) (n : Name) : LoomAssertionsMap :=
  let maxId := s.maxId + 1
  { s with maxId := maxId, syntaxStore := s.syntaxStore.insert maxId t, nameStore := s.nameStore.insert n maxId }

initialize loomAssertionsMap :
  SimplePersistentEnvExtension (Term × Name) LoomAssertionsMap <-
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s ⟨t, n⟩ => addAssertion s t n
    addImportedFn := fun as => Id.run do
      let mut res : LoomAssertionsMap := default
      for a in as do
        for (t, n) in a do
          res := addAssertion res t n
      return res
  }

section
variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u} [CompleteLattice l] [MPropOrdered m l]

set_option linter.unusedVariables false in
def invariantGadget {invType : Type u} (inv : List invType) [CompleteLattice invType] [MPropOrdered m invType] : m PUnit := pure .unit

declare_syntax_cat doneWith
declare_syntax_cat decreasingTerm
declare_syntax_cat invariantClause
declare_syntax_cat invariants
syntax "invariant" termBeforeDo linebreak : invariantClause
syntax "done_with" termBeforeDo : doneWith
syntax "decreasing" termBeforeDo : decreasingTerm

syntax (invariantClause linebreak)* : invariants

@[simp]
abbrev invariants (f : List l) := f.foldr (·⊓·) ⊤

-- macro "invariant" t:term : invariantClause => `(invariantGadget $t)


set_option linter.unusedVariables false in
def onDoneGadget {invType : Type u} (inv : invType) [CompleteLattice invType] [MPropOrdered m invType] : m PUnit := pure .unit


set_option linter.unusedVariables false in
def assertGadget {l : Type u} (h : l) [CompleteLattice l] [MPropOrdered m l] : m PUnit := pure .unit

macro "assert" t:term : term => `(assertGadget $t)

set_option linter.unusedVariables false in
def decreasingGadget (measure : ℕ) : m PUnit := pure .unit

macro "decreasing" t:term : term => `(decreasingGadget $t)

elab "with_name_prefix" lit:name inv:term : term => do
  let ⟨maxId, _, _⟩ <- loomAssertionsMap.get
  let newMaxId := maxId + 1
  let invName := lit.getName.toString ++ "_" ++ toString newMaxId.toNat |>.toName
  loomAssertionsMap.modify (fun res => {
      syntaxStore := res.syntaxStore.insert newMaxId inv
      nameStore := res.nameStore.insert invName newMaxId
      maxId := newMaxId
      })
  Term.elabTerm (<- ``(WithName $inv $(Lean.quoteNameMk invName))) none
  -- pure default

def termBeforeInvariant := Parser.withForbidden "invariant" Parser.termParser

attribute [run_builtin_parser_attribute_hooks] termBeforeInvariant

builtin_initialize
  register_parser_alias termBeforeInvariant

syntax "let" ident ":|" term : doElem
syntax "while" term
  (invariantClause)*
  doneWith
  "do" doSeq : doElem
syntax "while" term
  (invariantClause)*
  "do" doSeq : doElem
syntax "while" term
  (invariantClause)*
  decreasingTerm
  "do" doSeq : doElem
syntax "while" term
  (invariantClause)*
  doneWith
  decreasingTerm
  "do" doSeq : doElem
syntax "while_some" ident ":|" termBeforeDo "do" doSeq : doElem
syntax "while_some" ident ":|" term
  (invariantClause)*
  doneWith
  "do" doSeq : doElem
syntax "for" ident "in" termBeforeInvariant
  (invariantClause)+
  "do" doSeq : doElem

macro_rules
  | `(doElem| while $t
              $[invariant $inv:term
              ]*
              done_with $inv_done do $seq:doSeq) =>
      `(doElem|
        for _ in Lean.Loop.mk do
          invariantGadget [ $[(with_name_prefix `invariant $inv:term)],* ]
          onDoneGadget (with_name_prefix `done $inv_done:term)
          if $t then
            $seq:doSeq
          else break)
  | `(doElem| while $t
              $[invariant $inv:term
              ]*
              do $seq:doSeq) =>
      `(doElem|
        for _ in Lean.Loop.mk do
          invariantGadget [ $[(with_name_prefix `invariant $inv:term)],* ]
          onDoneGadget (with_name_prefix `done ¬$t:term)
          if $t then
            $seq:doSeq
          else break)
  | `(doElem| while $t
              $[invariant $inv:term
              ]*
              decreasing $measure:term
              do $seq:doSeq) =>
      `(doElem|
        for _ in Lean.Loop.mk do
          invariantGadget [ $[(with_name_prefix `invariant $inv:term)],* ]
          onDoneGadget (with_name_prefix `done ¬$t:term)
          decreasingGadget ($measure:term)
          if $t then
            $seq:doSeq
          else break)
  | `(doElem| while $t
              $[invariant $inv:term
              ]*
              done_with $inv_done
              decreasing $measure:term
              do $seq:doSeq) =>
      `(doElem|
        for _ in Lean.Loop.mk do
          invariantGadget [ $[(with_name_prefix `invariant $inv:term)],* ]
          onDoneGadget (with_name_prefix `done $inv_done:term)
          decreasingGadget ($measure:term)
          if $t then
            $seq:doSeq
          else break)
  | `(doElem| while_some $x:ident :| $t do $seq:doSeq) =>
    match seq with
    | `(doSeq| $[$seq:doElem]*)
    | `(doSeq| $[$seq:doElem;]*)
    | `(doSeq| { $[$seq:doElem]* }) =>
      `(doElem|
        while ∃ $x:ident, $t do
          let $x :| $t
          $[$seq:doElem]*)
    | _ => Lean.Macro.throwError "while_some expects a sequence of do-elements"
  | `(doElem| while_some $x:ident :| $t
              $[invariant $inv:term
              ]*
              done_with $inv_done do
                $seq:doSeq) =>
    match seq with
    | `(doSeq| $[$seq:doElem]*)
    | `(doSeq| $[$seq:doElem;]*)
    | `(doSeq| { $[$seq:doElem]* }) =>
      `(doElem|
        for _ in Lean.Loop.mk do
          invariantGadget [ $[(with_name_prefix `invariant $inv:term)],* ]
          onDoneGadget (with_name_prefix `done $inv_done:term)
          if ∃ $x:ident, $t then
            let $x :| $t
            $[$seq:doElem]*
          else break)
    | _ => Lean.Macro.throwError "while_some expects a sequence of do-elements"
  | `(doElem| for $x:ident in $t
            invariant $inv':term
            $[invariant $inv:term
            ]*
            do $seq:doSeq) =>
      match seq with
      | `(doSeq| $[$seq:doElem]*)
      | `(doSeq| $[$seq:doElem;]*)
      | `(doSeq| { $[$seq:doElem]* }) =>
        -- let inv := invs.push inv
        `(doElem|
          for $x:ident in $t do
            invariantGadget [ $inv':term, $[$inv:term],* ]
            $[$seq:doElem]*)
      | _ => Lean.Macro.throwError "for expects a sequence of do-elements"



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
    apply wp_cons; rintro (b'|b') <;> simp [triple]
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
variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u} [CompleteBooleanAlgebra l] [MPropOrdered m l]


def WPGen.assert {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MPropOrdered m l] (h : l) : WPGen (assertGadget (m := m) h) where
  get := fun post => h ⊓ (h ⇨ post .unit)
  prop := by simp [assertGadget, wp_pure]

noncomputable
def WPGen.if {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MPropOrdered m l]
  {_ : Decidable h} {x y : m α} (wpgx : WPGen x) (wpgy : WPGen y) : WPGen (if h then x else y) where
  get := fun post => (⌜WithName h (Lean.Name.anonymous.mkStr "if_pos")⌝ ⇨ wpgx.get post) ⊓ (⌜WithName (¬ h) (Lean.Name.anonymous.mkStr "if_neg")⌝ ⇨ wpgy.get post)
  prop := by
    intro post; simp [LE.pure]
    split <;> simp <;> solve_by_elim [wpgx.prop, wpgy.prop]

noncomputable
def WPGen.let  {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MPropOrdered m l]
  (y : β) {x : β -> m α} (wpgx : ∀ y, WPGen (x y)) : WPGen (let z := y; x z) where
  get := fun post => ⨅ z, ⌜z = y⌝ ⇨ (wpgx z).get post
  prop := by
     intro post; simp; refine iInf_le_of_le y ?_
     simp; apply (wpgx y).prop
