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
    wp (pure 7 : Id Nat) (fun n => p n ⊓ₗ q n) =
      wp (pure 7 : Id Nat) p ⊓ₗ wp (pure 7 : Id Nat) q := wp_and ..

example [IsHandler (fun (_ : String) => False)] :
    MAlgOrdered (ExceptT String Stack) (Bool → Nat → Order.Chain) := inferInstance

-- Bounds must stop parsing before the outer entailment/equality. Prop-index
-- simplification must rewrite the index domain, including list membership.
example [CompleteLattice α] (f : Nat → α) (a : α) :
    (⨅ₗ n, f n ⊑ₗ a) = (iInf f ⊑ₗ a) := rfl
example [CompleteLattice α] (f : Nat → α) : (⨆ₗ n, f n) = iSup f := rfl
example [CompleteLattice α] (f : Nat → α) (n : Nat) :
    (⨆ₗ k ∈ [n], f k) = f n := by simp

end

end LoomTest.Algebras
