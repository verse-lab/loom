import LoomMathlib.Order
import Loom.Order.Control
import Loom.MonadAlgebras.Defs

-- Merely importing Loom leaves mathlib's notation in effect.
example (p q : Prop) : (p ≤ q) = _root_.LE.le p q := rfl
example : (⊤ : Prop) = _root_.Top.top := rfl

open scoped Loom.Order

namespace LoomMathlibTest.Order

-- Both hierarchies retain their own proposition and function instances.
example : CompleteBooleanAlgebra (Nat → Prop) := inferInstance
example : Loom.Order.CompleteBooleanAlgebra (Nat → Prop) := inferInstance
example (p q : Nat → Prop) : (p ≤ q) = _root_.LE.le p q := rfl
example (p q : Nat → Prop) : (p ⊓ q) = _root_.Min.min p q := rfl
example (p q : Prop) : (p ⇨ q) = _root_.HImp.himp p q := rfl

-- The original embedding signature accepts any bounded relation.
section AbstractBoundedRelation
variable {α : Type u} [LE α] [OrderTop α] [OrderBot α]
local instance : Loom.Order.LE α := LoomMathlib.leOfMathlib α
local instance : Loom.Order.OrderTop α := LoomMathlib.orderTopOfMathlib α
local instance : Loom.Order.OrderBot α := LoomMathlib.orderBotOfMathlib α

example (a b : α) : (a ≤ b) = _root_.LE.le a b := rfl
example : (⌜True⌝ : α) = _root_.Top.top := trueE α
example : (⌜False⌝ : α) = _root_.Bot.bot := falseE α
example (p q : Prop) (h : p → q) : _root_.LE.le (⌜p⌝ : α) ⌜q⌝ := Loom.Order.embed_imp (l := α) p q h
example (p : Prop) (a : α) : _root_.LE.le (⌜p⌝ : α) a = (p → _root_.LE.le _root_.Top.top a) := Loom.Order.embed_intro p a
end AbstractBoundedRelation

section AbstractCompleteLattice
variable {α : Type u} [CompleteLattice α]
local instance : Loom.Order.CompleteLattice α := LoomMathlib.completeLatticeOfMathlib α

example (a b : α) : (a ≤ b) = _root_.LE.le a b := rfl
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
example (a b : α) : (a ⇨ b) = _root_.HImp.himp a b := rfl
example (a : α) : aᶜ = _root_.Compl.compl a := rfl
end AbstractBooleanAlgebra

section AbstractCompleteBooleanAlgebra
variable {α : Type u} [CompleteBooleanAlgebra α]
local instance : Loom.Order.CompleteBooleanAlgebra α :=
  LoomMathlib.completeBooleanAlgebraOfMathlib α

example (a : α) (f : Sort v → α) :
    _root_.Min.min a (iSup f) = iSup (fun i => _root_.Min.min a (f i)) := Loom.Order.inf_iSup a f
example (a : α) (f : Sort v → α) :
    _root_.Max.max a (iInf f) = iInf (fun i => _root_.Max.max a (f i)) := Loom.Order.sup_iInf a f

example : (LoomMathlib.completeBooleanAlgebraOfMathlib α).toCompleteLattice =
    LoomMathlib.completeLatticeOfMathlib α := rfl
example : (LoomMathlib.completeBooleanAlgebraOfMathlib α).toBooleanAlgebra =
    LoomMathlib.booleanAlgebraOfMathlib α := rfl
end AbstractCompleteBooleanAlgebra

-- In the Loom scope, prefer its relation even when mathlib has another one.
section ScopePriority
local instance : Loom.Order.LE Nat := ⟨fun a b => Nat.le b a⟩
example : (1 : Nat) ≤ 0 := Nat.zero_le 1
example : (0 : Nat) ≥ 1 := Nat.zero_le 1
example : ¬ _root_.LE.le (1 : Nat) 0 := by decide
end ScopePriority

-- Common symbols have unambiguous Loom meanings in a mixed import graph.
example (p q : Prop) : (p ⊔ q) = (p ∨ q) := rfl
example (p : Prop) : pᶜ = ¬p := rfl
example : (⊥ : Prop) = False := rfl
example (f : Nat → Prop) : (⨅ n, f n) = (∀ n, f n) := Loom.Order.prop_iInf f
example (f : Nat → Prop) : (⨆ n, f n) = (∃ n, f n) := Loom.Order.prop_iSup f
example (f : Nat → Prop) : (⨅ n : Nat, f n) = (∀ n, f n) := Loom.Order.prop_iInf f
example (f : Nat → Prop) : (⨆ n ∈ [0], f n) = f 0 := by simp

end LoomMathlibTest.Order
