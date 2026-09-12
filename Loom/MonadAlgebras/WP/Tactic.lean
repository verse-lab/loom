import Loom.MonadAlgebras.WP.Attr

open Loom Loom.Order

@[loomLogicSimp]
theorem leE (l : Type u) [PartialOrder l] (a b : α -> l) : a ⊑ₗ b ↔ ∀ x, a x ⊑ₗ b x := by
  rfl
@[loomLogicSimp]
theorem lePropE (a b : Prop) : (a ⊑ₗ b) = (a → b) := by
  rfl

@[loomLogicSimp]
theorem pureE (l : Type u) [CompleteLattice l] (a : Prop) : (⌜a⌝ : α -> l) = fun _ => ⌜a⌝ := by
  simp [Loom.Order.embed]; split <;> rfl

@[loomLogicSimp]
theorem purePropE  : (⌜a⌝ : Prop) = a := by
  simp [Loom.Order.embed]

@[loomLogicSimp]
theorem infPropE (a b : Prop) : (a ⊓ₗ b) = (a ∧ b) := by
  rfl

@[loomLogicSimp]
theorem infE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊓ₗ b) = fun x => a x ⊓ₗ b x := by
  rfl

@[loomLogicSimp]
theorem supE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊔ₗ b) = fun x => a x ⊔ₗ b x := by
  rfl

@[loomLogicSimp]
theorem supPropE (a b : Prop) : (a ⊔ₗ b) = (a ∨ b) := by
  rfl

@[loomLogicSimp]
theorem iInfE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨅ₗ i, a i) = fun x => ⨅ₗ i, a i x := by
  ext; simp

@[loomLogicSimp]
theorem iSupE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨆ₗ i, a i) = fun x => ⨆ₗ i, a i x := by
  ext; simp

@[loomLogicSimp]
theorem himpE  (l : Type u) [CompleteBooleanAlgebra l] (a b : α -> l) :
  (a ⇨ₗ b) = fun x => a x ⇨ₗ b x := by rfl

@[loomLogicSimp]
theorem himpPureE (a b : Prop) :
  (a ⇨ₗ b) = (a -> b) := by rfl

@[loomLogicSimp]
theorem topE (l : Type u) [CompleteLattice l] : (⊤ₗ : α -> l) = fun _ => ⊤ₗ := by rfl

@[loomLogicSimp]
theorem topPureE : (⊤ₗ : Prop) = True := by rfl

attribute [loomLogicSimp]
  forall_const
  implies_true and_true true_and
  prop_iInf prop_iSup
  and_imp
attribute [simp←] Nat.mul_add_one
