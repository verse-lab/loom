import LoomMathlib.Order
import Loom.Order.Control
import Loom.MonadAlgebras.Defs

-- Merely importing Loom leaves mathlib's notation in effect.
example : (⊤ : Prop) = _root_.Top.top := rfl
example (f : Nat → Prop) : (⨅ n, f n) = _root_.iInf f := rfl

namespace LoomMathlibTest.Order

-- Loom and mathlib register instances for the same Lean classes on `Prop` and
-- functions; the two agree definitionally and their lemmas apply to each other.
example (p q : Nat → Prop) : @LE.le _ Pi.hasLe p q = @LE.le _ Loom.Order.piCompleteLattice.toLE p q := rfl
example (p q : Prop) : @Min.min _ SemilatticeInf.toMin p q = @Min.min _ Loom.Order.propCompleteBooleanAlgebra.toMin p q := rfl
example (p q : Nat → Prop) (h : @LE.le _ Pi.hasLe p q) (n : Nat) (hp : p n) : q n := by
  rw [Loom.Order.pi_le_iff] at h; exact h n hp
example (p q : Nat → Prop) (h : @LE.le _ Loom.Order.piCompleteLattice.toLE p q) (n : Nat) (hp : p n) : q n := by
  rw [Pi.le_def] at h; exact h n hp
example (p q : Prop) (h : @Min.min _ SemilatticeInf.toMin p q) : p := by
  simp only [Loom.Order.prop_inf] at h; exact h.1
example : CompleteBooleanAlgebra (Nat → Prop) := inferInstance
example : Loom.Order.CompleteBooleanAlgebra (Nat → Prop) := inferInstance
example (p q : Nat → Prop) : Loom.Order.himp p q = _root_.HImp.himp p q := rfl
example (p : Nat → Prop) : Loom.Order.compl p = _root_.Compl.compl p := rfl

section AbstractCompleteLattice
variable {α : Type u} [CompleteLattice α]
local instance : Loom.Order.CompleteLattice α := LoomMathlib.completeLatticeOfMathlib α

example (a b : α) : a ⊓ b ≤ a := Std.min_le_left
example (s : α → Prop) : Loom.Order.sInf s = sInf s := rfl
example (s : α → Prop) : Loom.Order.sSup s = sSup s := rfl
example (f : Sort v → α) : Loom.Order.iInf f = iInf f := rfl
example (f : Sort v → α) : Loom.Order.iSup f = iSup f := rfl
example (p : Prop) (f : p → α) : Loom.Order.iInf f = iInf f := rfl
example (p : Prop) (f : p → α) : Loom.Order.iSup f = iSup f := rfl
example : (⌜True⌝ : α) = ⊤ := trueE α
example : (⌜False⌝ : α) = ⊥ := falseE α
example (p q : Prop) (h : p → q) : (⌜p⌝ : α) ≤ ⌜q⌝ := Loom.Order.embed_imp p q h
example (p : Prop) (a : α) : (⌜p⌝ ≤ a) = (p → ⊤ ≤ a) := Loom.Order.embed_intro p a
example : Loom.Order.CompleteLattice (Loom.Cont α Nat) := inferInstance
end AbstractCompleteLattice

section AbstractCompleteBooleanAlgebra
variable {α : Type u} [CompleteBooleanAlgebra α]
local instance : Loom.Order.CompleteBooleanAlgebra α :=
  LoomMathlib.completeBooleanAlgebraOfMathlib α

example (a : α) (f : Sort v → α) : a ⊓ iSup f = iSup (fun i => a ⊓ f i) :=
  Loom.Order.inf_iSup a f
example (a : α) (f : Sort v → α) : a ⊔ iInf f = iInf (fun i => a ⊔ f i) :=
  Loom.Order.sup_iInf a f
example (a : α) : Loom.Order.compl a = aᶜ := rfl
example (a b : α) : Loom.Order.himp a b = a ⇨ b := rfl
example : Loom.Order.CompleteBooleanAlgebra (Loom.Cont α Nat) := inferInstance
example : (LoomMathlib.completeBooleanAlgebraOfMathlib α).toCompleteLattice =
    LoomMathlib.completeLatticeOfMathlib α := rfl
end AbstractCompleteBooleanAlgebra

-- Under the Loom scope, common symbols resolve unambiguously next to mathlib.
section LoomScope
open scoped Loom.Order

example (p q : Prop) : (p ⊔ q) = (p ∨ q) := rfl
example (p q : Prop) : (p ⇨ q) = _root_.HImp.himp p q := rfl
example (p : Prop) : pᶜ = ¬p := rfl
example : (⊥ : Prop) = False := rfl
example (f : Nat → Prop) : (⨅ n, f n) = (∀ n, f n) := Loom.Order.prop_iInf f
example (f : Nat → Prop) : (⨆ n, f n) = (∃ n, f n) := Loom.Order.prop_iSup f
example (f : Nat → Prop) : (⨅ n : Nat, f n) = (∀ n, f n) := Loom.Order.prop_iInf f
example (n m : Nat) : (n ≤ m) = Nat.le n m := rfl
end LoomScope

open Loom.Order in
example (f : Nat → Prop) : (⨆ n ∈ [0], f n) = f 0 := by simp

end LoomMathlibTest.Order
