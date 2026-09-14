import Loom.Order.Instances
import Mathlib.Order.CompleteBooleanAlgebra

/-! Explicit conversions preserve the supplied mathlib operations. None is a
global instance: clients select a bridge with `letI` or `local instance`. -/

namespace LoomMathlib

universe u

@[implicit_reducible]
def leOfMathlib (α : Type u) [LE α] : Loom.Order.LE α where
  le := (· ≤ ·)

@[implicit_reducible]
def orderTopOfMathlib (α : Type u) [LE α] [OrderTop α] :
    @Loom.Order.OrderTop α (leOfMathlib α) := by
  letI := leOfMathlib α
  exact { top := ⊤, le_top := fun _ => le_top }

@[implicit_reducible]
def orderBotOfMathlib (α : Type u) [LE α] [OrderBot α] :
    @Loom.Order.OrderBot α (leOfMathlib α) := by
  letI := leOfMathlib α
  exact { bot := ⊥, bot_le := fun _ => bot_le }

@[implicit_reducible]
def preorderOfMathlib (α : Type u) [Preorder α] : Loom.Order.Preorder α where
  le := (· ≤ ·)
  toIsPreorder := inferInstanceAs (Std.IsPreorder α)

@[implicit_reducible]
def latticeOfMathlib (α : Type u) [Lattice α] : Loom.Order.Lattice α where
  le := (· ≤ ·)
  toIsPartialOrder := inferInstanceAs (Std.IsPartialOrder α)
  min := (· ⊓ ·)
  max := (· ⊔ ·)
  le_min_iff := fun _ _ _ => le_inf_iff
  max_le_iff := fun _ _ _ => sup_le_iff

@[implicit_reducible]
def completeLatticeOfMathlib (α : Type u) [CompleteLattice α] :
    Loom.Order.CompleteLattice α where
  toLattice := latticeOfMathlib α
  top := ⊤
  bot := ⊥
  le_top _ := le_top
  bot_le _ := bot_le
  sInf := sInf
  sSup := sSup
  sInf_le := sInf_le
  le_sInf := le_sInf
  le_sSup := le_sSup
  sSup_le := sSup_le

@[implicit_reducible]
def booleanAlgebraOfMathlib (α : Type u) [BooleanAlgebra α] :
    Loom.Order.BooleanAlgebra α where
  toLattice := latticeOfMathlib α
  top := ⊤
  bot := ⊥
  le_top _ := le_top
  bot_le _ := bot_le
  compl := Compl.compl
  himp := HImp.himp
  inf_sup_left := inf_sup_left
  inf_compl_eq_bot _ := inf_compl_eq_bot
  sup_compl_eq_top _ := sup_compl_eq_top
  himp_eq _ _ := himp_eq.trans (sup_comm ..)

@[implicit_reducible]
def completeBooleanAlgebraOfMathlib (α : Type u) [CompleteBooleanAlgebra α] :
    Loom.Order.CompleteBooleanAlgebra α :=
  { completeLatticeOfMathlib α, booleanAlgebraOfMathlib α with }

section CompleteLattice
variable {α : Type u} [CompleteLattice α]
local instance : Loom.Order.CompleteLattice α := completeLatticeOfMathlib α

theorem le_eq (a b : α) : Loom.Order.Preorder.le a b = (a ≤ b) := rfl
theorem inf_eq (a b : α) : Loom.Order.inf a b = a ⊓ b := rfl
theorem sup_eq (a b : α) : Loom.Order.sup a b = a ⊔ b := rfl
theorem sInf_eq (s : α → Prop) : Loom.Order.sInf s = sInf s := rfl
theorem sSup_eq (s : α → Prop) : Loom.Order.sSup s = sSup s := rfl

theorem iInf_eq {ι : Sort v} (f : ι → α) : Loom.Order.iInf f = iInf f := rfl
theorem iSup_eq {ι : Sort v} (f : ι → α) : Loom.Order.iSup f = iSup f := rfl
end CompleteLattice

end LoomMathlib
