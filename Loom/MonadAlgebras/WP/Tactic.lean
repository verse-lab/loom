import Loom.MonadAlgebras.WP.Attr

@[loomLogicSimp]
lemma leE (l : Type u) [PartialOrder l] (a b : α -> l) : a ≤ b ↔ ∀ x, a x ≤ b x := by
  rfl
@[loomLogicSimp]
lemma lePropE (a b : Prop) : (a ≤ b) = (a → b) := by
  rfl

@[loomLogicSimp]
lemma pureE (l : Type u) [CompleteLattice l] (a : Prop) : (⌜a⌝ : α -> l) = fun _ => ⌜a⌝ := by
  simp [LE.pure]; split <;> rfl

@[loomLogicSimp]
lemma purePropE  : (⌜a⌝ : Prop) = a := by
  simp [LE.pure]

@[loomLogicSimp]
lemma infPropE (a b : Prop) : (a ⊓ b) = (a ∧ b) := by
  rfl

@[loomLogicSimp]
lemma infE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊓ b) = fun x => a x ⊓ b x := by
  rfl

@[loomLogicSimp]
lemma supE (l : Type u) [CompleteLattice l] (a b : α -> l) : (a ⊔ b) = fun x => a x ⊔ b x := by
  rfl

@[loomLogicSimp]
lemma supPropE (a b : Prop) : (a ⊔ b) = (a ∨ b) := by
  rfl

@[loomLogicSimp]
lemma iInfE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨅ i, a i) = fun x => ⨅ i, a i x := by
  ext; simp

@[loomLogicSimp]
lemma iSupE (l : Type u) [CompleteLattice l] (a : ι -> α -> Prop) : (⨆ i, a i) = fun x => ⨆ i, a i x := by
  ext; simp

@[loomLogicSimp]
lemma himpE  (l : Type u) [CompleteBooleanAlgebra l] (a b : α -> l) :
  (a ⇨ b) = fun x => a x ⇨ b x := by rfl

@[loomLogicSimp]
lemma himpPureE (a b : Prop) :
  (a ⇨ b) = (a -> b) := by rfl

@[loomLogicSimp]
lemma topE (l : Type u) [CompleteLattice l] : (⊤ : α -> l) = fun _ => ⊤ := by rfl

@[loomLogicSimp]
lemma topPureE : (⊤ : Prop) = True := by rfl

attribute [loomLogicSimp]
  forall_const
  implies_true and_true true_and
  iInf_Prop_eq
  and_imp
attribute [simp←] Nat.mul_add_one
