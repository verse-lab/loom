module

public import Loom.MonadAlgebras.WP.Attr

@[expose] public section

open Loom Loom.Order

@[loomLogicSimp]
theorem leE (l : Type u) [CompleteLattice l] (a b : α -> l) : a ≤ b ↔ ∀ x, a x ≤ b x := by
  rfl
@[loomLogicSimp]
theorem lePropE (a b : Prop) : (a ≤ b) = (a → b) := by
  rfl

@[loomLogicSimp]
theorem pureE (l : Type u) [CompleteLattice l] (a : Prop) : (⌜a⌝ : α -> l) = fun _ => ⌜a⌝ := by
  simp [Loom.Order.embed]; split <;> rfl

@[loomLogicSimp]
theorem purePropE  : (⌜a⌝ : Prop) = a := by
  simp [Loom.Order.embed]

@[loomLogicSimp]
theorem infPropE (a b : Prop) : (a ⊓ b) = (a ∧ b) := by
  rfl

@[loomLogicSimp]
theorem infE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊓ b) = fun x => a x ⊓ b x := by
  rfl

@[loomLogicSimp]
theorem supE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊔ b) = fun x => a x ⊔ b x := by
  rfl

@[loomLogicSimp]
theorem supPropE (a b : Prop) : (a ⊔ b) = (a ∨ b) := by
  rfl

@[loomLogicSimp]
theorem iInfE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨅ i, a i) = fun x => ⨅ i, a i x := by
  ext; simp

@[loomLogicSimp]
theorem iSupE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨆ i, a i) = fun x => ⨆ i, a i x := by
  ext; simp

@[loomLogicSimp]
theorem himpE  (l : Type u) [CompleteBooleanAlgebra l] (a b : α -> l) :
  (a ⇨ b) = fun x => a x ⇨ b x := by rfl

@[loomLogicSimp]
theorem himpPureE (a b : Prop) :
  (a ⇨ b) = (a -> b) := by rfl

@[loomLogicSimp]
theorem topE (l : Type u) [CompleteLattice l] : (⊤ : α -> l) = fun _ => ⊤ := by rfl

@[loomLogicSimp]
theorem topPureE : (⊤ : Prop) = True := by rfl

attribute [loomLogicSimp]
  forall_const
  implies_true and_true true_and
  prop_iInf prop_iSup
  and_imp
attribute [simp←] Nat.mul_add_one
