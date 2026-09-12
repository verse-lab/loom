import Loom.Order.Control

open Loom.Order

namespace LoomTest.Order

/-- A complete lattice whose middle element has no Boolean complement. -/
inductive Chain where
  | low | middle | high
  deriving DecidableEq

namespace Chain

def rank : Chain → Nat
  | low => 0 | middle => 1 | high => 2

instance : Lattice Chain where
  le a b := rank a ≤ rank b
  le_refl _ := Nat.le_refl _
  le_trans := Nat.le_trans
  le_antisymm := by
    intro a b; cases a <;> cases b <;> simp_all [rank]
  inf a b := if rank a ≤ rank b then a else b
  sup a b := if rank a ≤ rank b then b else a
  inf_le_left := by intro a b; cases a <;> cases b <;> decide
  inf_le_right := by intro a b; cases a <;> cases b <;> decide
  le_inf := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  le_sup_left := by intro a b; cases a <;> cases b <;> decide
  le_sup_right := by intro a b; cases a <;> cases b <;> decide
  sup_le := by intro a b c; cases a <;> cases b <;> cases c <;> decide

instance (a b : Chain) : Decidable (a ⊑ₗ b) :=
  inferInstanceAs (Decidable (rank a ≤ rank b))

noncomputable def meet (s : Chain → Prop) : Chain := by
  classical
  exact if s low then low else if s middle then middle else high

noncomputable def join (s : Chain → Prop) : Chain := by
  classical
  exact if s high then high else if s middle then middle else low

noncomputable instance : CompleteLattice Chain where
  toLattice := inferInstance
  top := high
  bot := low
  le_top := by intro a; cases a <;> decide
  bot_le := by intro a; cases a <;> decide
  sInf := meet
  sSup := join
  sInf_le := by
    classical
    intro s a ha
    change rank (meet s) ≤ rank a
    by_cases hl : s low <;> by_cases hm : s middle <;>
      cases a <;> simp_all [meet, rank]
  le_sInf := by
    classical
    intro s a h
    change rank a ≤ rank (meet s)
    unfold meet
    split
    · exact h _ ‹s low›
    · split
      · exact h _ ‹s middle›
      · cases a <;> decide
  le_sSup := by
    classical
    intro s a ha
    change rank a ≤ rank (join s)
    by_cases hh : s high <;> by_cases hm : s middle <;>
      cases a <;> simp_all [join, rank]
  sSup_le := by
    classical
    intro s a h
    change rank (join s) ≤ rank a
    unfold join
    split
    · exact h _ ‹s high›
    · split
      · exact h _ ‹s middle›
      · cases a <;> decide

-- The model really is non-Boolean: the middle element has no complement.
example : ¬ ∃ c : Chain, middle ⊓ₗ c = bot ∧ middle ⊔ₗ c = top := by
  rintro ⟨c, h⟩
  cases c <;> cases h with
  | intro h₁ h₂ => contradiction

example : iSup (fun b : Bool => if b then middle else low) = middle := by
  apply le_antisymm
  · apply iSup_le
    intro b; cases b <;> decide
  · exact le_iSup (fun b : Bool => if b then middle else low) true

example : iInf (fun _ : Empty => middle) = high := iInf_of_empty Empty.elim _

end Chain

-- Small assumptions remain enough for wrapper instances.
example [Preorder α] : Preorder (Loom.Cont α Nat) := inferInstance
example [BooleanAlgebra α] : BooleanAlgebra (Loom.Cont α Nat) := inferInstance
example [CompleteLattice α] : CompleteLattice (Loom.Cont α Nat) := inferInstance

-- Both parent paths preserve precisely the same operations and order.
example (h : CompleteBooleanAlgebra α) :
    h.toCompleteLattice.toLattice = h.toBooleanAlgebra.toLattice := rfl
example (h : CompleteBooleanAlgebra α) :
    h.toCompleteLattice.toOrderTop = h.toBooleanAlgebra.toOrderTop := rfl
example (h : CompleteBooleanAlgebra α) :
    h.toCompleteLattice.toOrderBot = h.toBooleanAlgebra.toOrderBot := rfl

-- Nested state/reader predicates and genuinely dependent carrier families.
example : CompleteBooleanAlgebra (Nat → Bool → Prop) := inferInstance
noncomputable example : CompleteLattice ((b : Bool) → if b then Prop else Chain) := by
  haveI : ∀ b : Bool, CompleteLattice (if b then Prop else Chain) := fun b => by
    cases b <;> simp <;> exact inferInstance
  exact inferInstance
example (p q : Nat → Bool → Prop) (s : Nat) (r : Bool) :
    himp p q s r = (p s r → q s r) := rfl
example (p q : Nat → Bool → Prop) :
    (p ⊑ₗ q) = (∀ s r, p s r → q s r) := rfl

-- Index universes are independent of the carrier and include propositions.
example (f : Sort u → Prop) : iInf f = (∀ i, f i) := prop_iInf f
example [CompleteLattice α] (p : Prop) (f : p → α) (hp : p) :
    iInf f = f hp := by
  exact le_antisymm (iInf_le f hp) (le_iInf fun _ => le_refl _)
example (p : Prop) (f : p → Prop) : iSup f = (∃ hp, f hp) := prop_iSup f
example (f : Nat → Bool → Prop) (b : Bool) :
    iInf f b = (∀ n, f n b) := by simp

example [CompleteBooleanAlgebra α] (a : α) (f : Sort u → α) :
    a ⊓ₗ iSup f = iSup (fun i => a ⊓ₗ f i) := inf_iSup a f
example [CompleteBooleanAlgebra α] (a : α) (f : Sort u → α) :
    a ⊔ₗ iInf f = iInf (fun i => a ⊔ₗ f i) := sup_iInf a f

end LoomTest.Order
