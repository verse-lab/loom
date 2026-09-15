import Loom.Order.Instances
import Mathlib.Order.CompleteBooleanAlgebra

/-! Explicit conversions from mathlib's bundled orders. Loom shares Lean's
`LE`/`Min`/`Max`, so only bounds, complement, and implication are supplied. -/

namespace LoomMathlib

universe u v

@[implicit_reducible]
def completeLatticeOfMathlib (α : Type u) [CompleteLattice α] :
    Loom.Order.CompleteLattice α where
  toIsPartialOrder := inferInstanceAs (Std.IsPartialOrder α)
  le_min_iff _ _ _ := le_inf_iff
  max_le_iff _ _ _ := sup_le_iff
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
def completeBooleanAlgebraOfMathlib (α : Type u) [CompleteBooleanAlgebra α] :
    Loom.Order.CompleteBooleanAlgebra α where
  toCompleteLattice := completeLatticeOfMathlib α
  compl := Compl.compl
  himp := HImp.himp
  inf_sup_left := inf_sup_left
  inf_compl_eq_bot _ := inf_compl_eq_bot
  sup_compl_eq_top _ := sup_compl_eq_top
  himp_eq _ _ := himp_eq.trans (sup_comm ..)

section CompleteLattice
variable {α : Type u} [CompleteLattice α]
local instance : Loom.Order.CompleteLattice α := completeLatticeOfMathlib α

theorem iInf_eq {ι : Sort v} (f : ι → α) : Loom.Order.iInf f = iInf f := rfl
theorem iSup_eq {ι : Sort v} (f : ι → α) : Loom.Order.iSup f = iSup f := rfl
end CompleteLattice

end LoomMathlib
