import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import LoL.MonadAlgebras.WP.Basic
import LoL.MonadAlgebras.WP.Liberal

universe u v w

section
variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u} [CompleteLattice l] [MPropOrdered m l]

set_option linter.unusedVariables false in
def invariantGadget {invType : Type w} (inv : invType) : m PUnit := pure .unit


macro "invariant" t:term : term => `(invariantGadget $t)


set_option linter.unusedVariables false in
def onDoneGadget {invType : Type w} (inv : invType) : m PUnit := pure .unit


set_option linter.unusedVariables false in
def assertGadget {l : Type w} (h : l) : m PUnit := pure .unit

macro "assert" t:term : term => `(assertGadget $t)

set_option linter.unusedVariables false in
def decreasingGadget (measure : ℕ) : m PUnit := pure .unit

macro "decreasing" t:term : term => `(decreasingGadget $t)

syntax "let" ident ":|" term : doElem
syntax "while" term
  "invariant" term
  "on_done" termBeforeDo
  "do" doSeq : doElem
syntax "while_some" ident ":|" termBeforeDo "do" doSeq : doElem
syntax "while_some" ident ":|" term
  "invariant" term
  "on_done" termBeforeDo
  "do" doSeq : doElem
macro_rules
  | `(doElem| let $x:ident :| $t) => `(doElem| let $x:ident <- pickSuchThat _ (fun $x => $t))
  | `(doElem| while $t
              invariant $inv_yield
              on_done $inv_done do $seq:doSeq) =>
    match seq with
    | `(doSeq| $[$seq:doElem]*)
    | `(doSeq| $[$seq:doElem;]*)
    | `(doSeq| { $[$seq:doElem]* }) =>
      `(doElem| while $t do
          invariantGadget $inv_yield
          onDoneGadget $inv_done
          $[$seq:doElem]*)
    | _ => Lean.Macro.throwError "while expects a sequence of do-elements"
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
              invariant $inv_yield
              on_done $inv_done do
                $seq:doSeq) =>
    match seq with
    | `(doSeq| $[$seq:doElem]*)
    | `(doSeq| $[$seq:doElem;]*)
    | `(doSeq| { $[$seq:doElem]* }) =>
      `(doElem|
        for _ in Lean.Loop.mk do
          invariantGadget $inv_yield
          onDoneGadget $inv_done
          if ∃ $x:ident, $t then
            let $x :| $t
            $[$seq:doElem]*
          else break)
    | _ => Lean.Macro.throwError "while_some expects a sequence of do-elements"


structure WPGen (x : m α) where
  get : Cont l α
  invs : Prop := True
  prop : ∀ post, invs -> get post <= wp x post

omit [LawfulMonad m] in
lemma WPGen.intro (x : m α) (wpg : WPGen x) :
  wpg.invs -> pre <= wpg.get post ->
  triple pre x post := by
  solve_by_elim [wpg.prop, le_trans']

def WPGen.default (x : m α) : WPGen x where
  get := wp x
  prop := by intro post; simp_all only [le_refl]; trivial

def WPGen.pure (x : α) : WPGen (pure (f := m) x) where
  get := fun post => post x
  prop := by intro post; simp_all only [wp_pure, le_refl]; trivial

def WPGen.bind (x : m α) (f : α -> m β) (wpg : WPGen x) (wpgf : ∀ a, WPGen (f a)) :
  WPGen (x >>= f) where
  get := fun post => wpg.get (fun a => (wpgf a).get post)
  invs := wpg.invs ∧ ∀ a, (wpgf a).invs
  prop := by
    simp; intro post invs invs'; simp [wp_bind]; apply le_trans
    { solve_by_elim [wpg.prop] }
    apply wp_cons; intro a; solve_by_elim [(wpgf a).prop]

def WPGen.map (x : m α) (f : α -> β) (wpg : WPGen x) : WPGen (f <$> x) where
  get := fun post => wpg.get (fun a => post (f a))
  invs := wpg.invs
  prop := by
    intro _ _
    rw [map_eq_pure_bind]; simp only [wp_bind, wp_pure]
    apply le_trans; solve_by_elim [wpg.prop]; rfl


noncomputable
def WPGen.spec_triple (x : m α) (trp : triple pre x post) : WPGen x where
  get := spec pre post
  prop := by rw [<-triple_spec] at trp; solve_by_elim

noncomputable
def WPGen.spec_triple_invs (x : m α) (invs : Prop) (trp : invs -> triple pre x post) : WPGen x where
  get := spec pre post
  invs := invs
  prop := by rw [<-triple_spec] at trp; solve_by_elim

def WPGen.spec_wp wp' (x : m α) (trp : wp x = wp') : WPGen x where
  get := wp'
  prop := by
    intro post
    subst trp
    simp_all only [le_refl]; trivial

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

noncomputable
def WPGen.forWithInvariant {xs : Std.Range} {init : β} {f : ℕ → β → m (ForInStep β)}
  (inv : ℕ → β → l) :
    xs.step = 1 ->
    xs.start <= xs.stop ->
    WPGen (forIn xs init (fun i b => do invariantGadget (inv i b); (f i b))) := by
    intro stp _
    apply spec_triple_invs (invs :=
      (∀ i b, triple (inv i b) (f i b) (fun | .yield b' => inv (i + 1) b' | .done b' => inv xs.stop b')));
    intros h; apply triple_forIn_range_step1 inv; simp [invariantGadget, stp]; apply h
    all_goals solve_by_elim

noncomputable
def WPGen.forWithInvariantDecreasing {β} {measure : β -> ℕ}
  {init : β} {f : β → m (ForInStep β)}
  (inv : β → l) :
    WPGen (forIn [0:mb] init (fun _ b => do decreasingGadget (measure b); invariantGadget (inv b); f b)) := by
  apply spec_triple_invs (invs :=
    mb = measure init ∧
    (∀ b, measure b <= measure init -> triple (inv b) (f b) (fun | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝ | .done b' => ⌜ measure b' = 0 ⌝ ⊓ inv b')))
  simp only [and_imp]; intros eq h; simp only [eq]
  apply triple_forIn_deacreasing inv; simp [invariantGadget, decreasingGadget]
  all_goals solve_by_elim
end
variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u} [CompleteBooleanAlgebra l] [MPropOrdered m l]


def WPGen.assert {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MPropOrdered m l] (h : l) : WPGen (assertGadget (m := m) h) where
  get := fun post => h ⊓ (h ⇨ post .unit)
  prop := by simp [assertGadget, wp_pure]

def WPGen.if [Decidable h] (x y : m α) (wpgx : WPGen x) (wpgy : WPGen y) : WPGen (if h then x else y) where
  get := fun post => if h then wpgx.get post else wpgy.get post
  invs := if h then wpgx.invs else wpgy.invs
  prop := by
    intro post; split <;> solve_by_elim [wpgx.prop, wpgy.prop]
