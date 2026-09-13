import LoomMathlib.Order
import Loom.Order.Control
import Loom.MonadAlgebras.Defs

open scoped Loom.Order

namespace LoomMathlibTest.Order

-- Both hierarchies retain their own proposition and function instances.
example : CompleteBooleanAlgebra (Nat → Prop) := inferInstance
example : Loom.Order.CompleteBooleanAlgebra (Nat → Prop) := inferInstance
example (p q : Nat → Prop) : (p ≤ q) = (p ⊑ₗ q) := rfl
example (p q : Nat → Prop) : (p ⊓ q) = (p ⊓ₗ q) := rfl
example (p q : Prop) : (p ⇨ q) = Loom.Order.himp p q := rfl

-- The original embedding signature accepts any bounded relation.
section AbstractBoundedRelation
variable {α : Type u} [LE α] [OrderTop α] [OrderBot α]
local instance : Loom.Order.LE α := LoomMathlib.leOfMathlib α
local instance : Loom.Order.OrderTop α := LoomMathlib.orderTopOfMathlib α
local instance : Loom.Order.OrderBot α := LoomMathlib.orderBotOfMathlib α

example (a b : α) : (a ⊑ₗ b) = (a ≤ b) := rfl
example : (⌜True⌝ : α) = ⊤ := trueE α
example : (⌜False⌝ : α) = ⊥ := falseE α
example (p q : Prop) (h : p → q) : (⌜p⌝ : α) ≤ ⌜q⌝ := Loom.Order.embed_imp (l := α) p q h
example (p : Prop) (a : α) : ((⌜p⌝ : α) ≤ a) = (p → ⊤ ≤ a) := Loom.Order.embed_intro p a
end AbstractBoundedRelation

section AbstractCompleteLattice
variable {α : Type u} [CompleteLattice α]
local instance : Loom.Order.CompleteLattice α := LoomMathlib.completeLatticeOfMathlib α

example (a b : α) : (a ⊑ₗ b) = (a ≤ b) := rfl
example (f : Sort v → α) : Loom.Order.iInf f = iInf f := rfl
example (f : Sort v → α) : Loom.Order.iSup f = iSup f := rfl
example (p : Prop) (f : p → α) : Loom.Order.iInf f = iInf f := rfl
example : Loom.Order.CompleteLattice (Loom.Cont α Nat) := inferInstance
end AbstractCompleteLattice

section AbstractBooleanAlgebra
variable {α : Type u} [BooleanAlgebra α]
local instance : Loom.Order.BooleanAlgebra α := LoomMathlib.booleanAlgebraOfMathlib α

-- Continuation inversion can remain Boolean-only, without completeness.
example : Loom.Order.BooleanAlgebra (Loom.Cont α Nat) := inferInstance
example (a b : α) : Loom.Order.himp a b = a ⇨ b := rfl
example (a : α) : Loom.Order.compl a = aᶜ := rfl
end AbstractBooleanAlgebra

section AbstractCompleteBooleanAlgebra
variable {α : Type u} [CompleteBooleanAlgebra α]
local instance : Loom.Order.CompleteBooleanAlgebra α :=
  LoomMathlib.completeBooleanAlgebraOfMathlib α

example (a : α) (f : Sort v → α) :
    a ⊓ iSup f = iSup (fun i => a ⊓ f i) := Loom.Order.inf_iSup a f
example (a : α) (f : Sort v → α) :
    a ⊔ iInf f = iInf (fun i => a ⊔ f i) := Loom.Order.sup_iInf a f

example : (LoomMathlib.completeBooleanAlgebraOfMathlib α).toCompleteLattice =
    LoomMathlib.completeLatticeOfMathlib α := rfl
example : (LoomMathlib.completeBooleanAlgebraOfMathlib α).toBooleanAlgebra =
    LoomMathlib.booleanAlgebraOfMathlib α := rfl
end AbstractCompleteBooleanAlgebra

end LoomMathlibTest.Order
