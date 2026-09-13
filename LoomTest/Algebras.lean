import Loom
import LoomTest.Order

open Loom Loom.Order

namespace LoomTest.Algebras

noncomputable section

-- An algebra still needs no assertion order at all.
example (α : Type) : MAlg Id α where
  μ := id
  pure _ := rfl
  bind x _ _ h := congrFun h x

-- Exercise the actual WP and transformer interfaces over a non-Boolean model.
noncomputable local instance : MAlgOrdered Id Order.Chain where
  μ := id
  μ_ord_pure _ := rfl
  μ_ord_bind _ _ h x := h x

local instance : MAlgDet Id Order.Chain where
  demonic _ _ _ := le_refl _
  angelic _ _ _ := le_refl _

abbrev Stack := ReaderT Bool (StateT Nat Id)

example : MAlgOrdered Stack (Bool → Nat → Order.Chain) := inferInstance
example : MAlgDet Stack (Bool → Nat → Order.Chain) := inferInstance

example (p q : Nat → Order.Chain) :
    wp (pure 7 : Id Nat) (fun n => p n ⊓ q n) =
      wp (pure 7 : Id Nat) p ⊓ wp (pure 7 : Id Nat) q := wp_and ..

example [IsHandler (fun (_ : String) => False)] :
    MAlgOrdered (ExceptT String Stack) (Bool → Nat → Order.Chain) := inferInstance

-- Bounds must stop parsing before the outer entailment/equality. Prop-index
-- simplification must rewrite the index domain, including list membership.
example [CompleteLattice α] (f : Nat → α) (a : α) :
    (⨅ n, f n ≤ a) = (iInf f ≤ a) := rfl
example [CompleteLattice α] (f : Nat → α) : (⨆ n, f n) = iSup f := rfl
example [CompleteLattice α] (f : Nat → α) (n : Nat) :
    (⨆ k ∈ [n], f k) = f n := by simp

end

-- Embedding needs bounds on a relation, not reflexivity or transitivity.
namespace BareBounds

inductive Carrier where
  | low | middle | high

instance : Loom.Order.LE Carrier where
  le a b := a = .low ∨ b = .high

instance : OrderTop Carrier where
  top := .high
  le_top _ := Or.inr rfl

instance : OrderBot Carrier where
  bot := .low
  bot_le _ := Or.inl rfl

example : ¬ (Carrier.middle ≤ Carrier.middle) := by
  intro h
  cases h with
  | inl h => cases h
  | inr h => cases h

example : (⌜True⌝ : Carrier) = Carrier.high := trueE Carrier
example : (⌜False⌝ : Carrier) = Carrier.low := falseE Carrier
example (p q : Prop) (h : p → q) : (⌜p⌝ : Carrier) ≤ ⌜q⌝ := embed_imp p q h
example (p : Prop) (a : Carrier) : (⌜p⌝ ≤ a) = (p → ⊤ ≤ a) := embed_intro p a

-- Weak bounds also propagate through the standard assertion wrappers.
example : OrderTop (Id Carrier) := inferInstance
example : OrderBot (Id Carrier) := inferInstance
example : (⌜True⌝ : Nat → Carrier) = fun _ => Carrier.high := trueE _
example : (⌜False⌝ : Loom.Cont Carrier Nat) = fun _ => Carrier.low := falseE _

end BareBounds

section BareRelation
variable [Loom.Order.LE α] [OrderTop α] [OrderBot α]
example (p q : Prop) (h : p → q) : (⌜p⌝ : α) ≤ ⌜q⌝ := embed_imp p q h
example (p : Prop) (a : α) : (⌜p⌝ ≤ a) = (p → ⊤ ≤ a) := embed_intro p a
end BareRelation

-- Familiar notation selects Loom assertions and preserves numeric comparisons.
example [Loom.Order.Preorder α] (a : α) : a <= a := Loom.Order.le_refl a
example [Loom.Order.Preorder α] (a : α) : a >= a := Loom.Order.le_refl a
example (p : Prop) : p ≤ ⊤ := Loom.Order.le_top p
example (p : Prop) : ⊥ ≤ p := Loom.Order.bot_le p
example (p q : Prop) : (p ≥ q) = (q → p) := rfl
example (p q : Prop) : (p ⇨ q) = (p → q) := rfl
example (p : Prop) : pᶜ = ¬p := rfl
def defaultNumericComparison := fun n => n ≤ 1
example : defaultNumericComparison 0 := by unfold defaultNumericComparison; decide
example (n m : Nat) (h : Nat.le n m) : Nat.le n m := by
  change (_ : Nat) ≤ _
  exact h
example (n m : Nat) : (n ≤ m) = Nat.le n m := rfl
example (n m : Int) : (n ≥ m) = Int.le m n := rfl
example (n m : Nat) (h : n ≤ m) : n < m + 1 := by omega
example (n m : Int) (h : n ≤ m) : n < m + 1 := by omega

end LoomTest.Algebras
