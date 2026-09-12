import Loom.Order.CompleteLattice

namespace Loom.Order

universe u v

/-- A bounded distributive complemented lattice. Implication is an explicit
operation so the proposition model can reduce directly to Lean implication. -/
class BooleanAlgebra (α : Type u) extends Lattice α, OrderTop α, OrderBot α where
  compl : α → α
  himp : α → α → α
  inf_sup_left : ∀ (a b c : α), a ⊓ₗ (b ⊔ₗ c) = (a ⊓ₗ b) ⊔ₗ (a ⊓ₗ c)
  inf_compl_eq_bot : ∀ a, a ⊓ₗ compl a = bot
  sup_compl_eq_top : ∀ a, a ⊔ₗ compl a = top
  himp_eq : ∀ a b, himp a b = compl a ⊔ₗ b

/-- Completeness adds no distributivity or atomicity axiom. The shared lattice,
top, and bottom fields on the two inheritance paths are definitionally equal. -/
class CompleteBooleanAlgebra (α : Type u) extends CompleteLattice α, BooleanAlgebra α

export BooleanAlgebra (compl himp inf_sup_left inf_compl_eq_bot sup_compl_eq_top himp_eq)

attribute [simp] inf_compl_eq_bot sup_compl_eq_top

variable {α : Type u}

section Boolean
variable [BooleanAlgebra α] {a b c : α}

theorem inf_sup_right (a b c : α) : (a ⊔ₗ b) ⊓ₗ c = (a ⊓ₗ c) ⊔ₗ (b ⊓ₗ c) := by
  rw [inf_comm, inf_sup_left, inf_comm c a, inf_comm c b]

/-- Boolean implication is right adjoint to meet. -/
theorem le_himp_iff : a ⊑ₗ himp b c ↔ a ⊓ₗ b ⊑ₗ c := by
  rw [himp_eq]
  constructor
  · intro h
    have k := inf_mono h (le_refl b)
    rw [inf_sup_right, inf_comm (compl b) b, inf_compl_eq_bot, bot_sup] at k
    exact le_trans k (inf_le_left ..)
  · intro h
    have k : a = (a ⊓ₗ b) ⊔ₗ (a ⊓ₗ compl b) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top]
    rw [k]
    exact sup_le (le_trans h (le_sup_right ..))
      (le_trans (inf_le_right ..) (le_sup_left ..))

theorem le_compl_iff : a ⊑ₗ compl b ↔ a ⊓ₗ b ⊑ₗ bot := by
  have h := le_himp_iff (a := a) (b := b) (c := bot)
  simpa only [himp_eq, sup_bot] using h

theorem compl_antitone (h : a ⊑ₗ b) : compl b ⊑ₗ compl a := by
  apply le_compl_iff.mpr
  have k := inf_mono (le_refl (compl b)) h
  rw [inf_comm (compl b) b, inf_compl_eq_bot] at k
  exact k

@[simp] theorem compl_compl (a : α) : compl (compl a) = a := by
  have lower : a ⊑ₗ compl (compl a) := le_compl_iff.mpr (by simp)
  have upper : compl (compl a) ⊑ₗ a := by
    have k : compl (compl a) =
        (compl (compl a) ⊓ₗ a) ⊔ₗ (compl (compl a) ⊓ₗ compl a) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top]
    rw [k, inf_comm (compl (compl a)) (compl a), inf_compl_eq_bot, sup_bot]
    exact inf_le_right ..
  exact le_antisymm upper lower

theorem compl_le_iff_compl_le : compl a ⊑ₗ b ↔ compl b ⊑ₗ a := by
  constructor <;> intro h
  · simpa only [compl_compl] using compl_antitone h
  · simpa only [compl_compl] using compl_antitone h

theorem compl_sup (a b : α) : compl (a ⊔ₗ b) = compl a ⊓ₗ compl b := by
  apply le_antisymm
  · exact le_inf (compl_antitone (le_sup_left ..)) (compl_antitone (le_sup_right ..))
  · apply le_compl_iff.mpr
    rw [inf_sup_left]
    apply sup_le
    · exact le_trans (inf_mono (inf_le_left ..) (le_refl a))
        (by rw [inf_comm, inf_compl_eq_bot]; exact le_refl _)
    · exact le_trans (inf_mono (inf_le_right ..) (le_refl b))
        (by rw [inf_comm, inf_compl_eq_bot]; exact le_refl _)

theorem compl_inf (a b : α) : compl (a ⊓ₗ b) = compl a ⊔ₗ compl b := by
  have h := congrArg compl (compl_sup (compl a) (compl b))
  simpa only [compl_compl] using h.symm

@[simp] theorem compl_top : compl (top : α) = bot := by
  have h := inf_compl_eq_bot (top : α)
  simpa only [top_inf] using h

@[simp] theorem compl_bot : compl (bot : α) = top := by
  have h := sup_compl_eq_top (bot : α)
  simpa only [bot_sup] using h

theorem sup_inf_left (a b c : α) : a ⊔ₗ (b ⊓ₗ c) = (a ⊔ₗ b) ⊓ₗ (a ⊔ₗ c) := by
  have h := congrArg compl (inf_sup_left (compl a) (compl b) (compl c))
  simpa only [compl_inf, compl_sup, compl_compl] using h

end Boolean

section CompleteBoolean
variable [CompleteBooleanAlgebra α]

theorem compl_iSup {ι : Sort v} (f : ι → α) :
    compl (iSup f) = iInf (fun i => compl (f i)) := by
  apply le_antisymm
  · exact le_iInf fun i => compl_antitone (le_iSup f i)
  · have h : iSup f ⊑ₗ compl (iInf (fun i => compl (f i))) := by
      apply iSup_le
      intro i
      simpa only [compl_compl] using
        compl_antitone (iInf_le (fun i => compl (f i)) i)
    simpa only [compl_compl] using compl_antitone h

theorem compl_iInf {ι : Sort v} (f : ι → α) :
    compl (iInf f) = iSup (fun i => compl (f i)) := by
  have h := congrArg compl (compl_iSup (fun i => compl (f i)))
  simpa only [compl_compl] using h.symm

/-- Finite meets distribute over arbitrary joins in every complete Boolean
algebra; this follows from the implication adjunction, not an extra axiom. -/
theorem inf_iSup {ι : Sort v} (a : α) (f : ι → α) :
    a ⊓ₗ iSup f = iSup (fun i => a ⊓ₗ f i) := by
  apply le_antisymm
  · rw [inf_comm]
    apply le_himp_iff.mp
    apply iSup_le
    intro i
    apply le_himp_iff.mpr
    rw [inf_comm]
    exact le_iSup (fun i => a ⊓ₗ f i) i
  · exact iSup_le fun i => inf_mono (le_refl a) (le_iSup f i)

theorem sup_iInf {ι : Sort v} (a : α) (f : ι → α) :
    a ⊔ₗ iInf f = iInf (fun i => a ⊔ₗ f i) := by
  have h := congrArg compl (inf_iSup (compl a) (fun i => compl (f i)))
  simpa only [compl_inf, compl_iSup, compl_compl] using h

end CompleteBoolean

section Simp
variable [BooleanAlgebra α] {a b c : α}

theorem himp_eq_sup_compl (a b : α) : himp a b = b ⊔ₗ compl a := by
  rw [himp_eq, sup_comm]

@[simp] theorem compl_le_compl_iff : compl a ⊑ₗ compl b ↔ b ⊑ₗ a :=
  ⟨fun h => by simpa only [compl_compl] using compl_antitone h, compl_antitone⟩

theorem le_himp_iff' : a ⊑ₗ himp b c ↔ b ⊓ₗ a ⊑ₗ c := by
  rw [le_himp_iff, inf_comm]

@[simp] theorem himp_self (a : α) : himp a a = top := by
  rw [himp_eq_sup_compl, sup_compl_eq_top]

@[simp] theorem top_himp (a : α) : himp top a = a := by simp [himp_eq]
@[simp] theorem bot_himp (a : α) : himp bot a = top := by simp [himp_eq]
@[simp] theorem himp_top (a : α) : himp a top = top := by simp [himp_eq]

theorem eq_top_iff : a = top ↔ top ⊑ₗ a := top_le_iff.symm

@[simp] theorem compl_inf_eq_bot (a : α) : compl a ⊓ₗ a = bot := by
  rw [inf_comm, inf_compl_eq_bot]

@[simp] theorem compl_sup_eq_top (a : α) : compl a ⊔ₗ a = top := by
  rw [sup_comm, sup_compl_eq_top]

theorem compl_le_iff : compl a ⊑ₗ b ↔ top ⊑ₗ a ⊔ₗ b := by
  simpa only [himp_eq, top_inf, compl_compl] using
    (le_himp_iff (a := top) (b := compl a) (c := b)).symm

theorem inf_inf_distrib_right (a b c : α) :
    (a ⊓ₗ b) ⊓ₗ c = (a ⊓ₗ c) ⊓ₗ (b ⊓ₗ c) := by
  apply le_antisymm
  · exact le_inf (le_inf (le_trans (inf_le_left ..) (inf_le_left ..)) (inf_le_right ..))
      (le_inf (le_trans (inf_le_left ..) (inf_le_right ..)) (inf_le_right ..))
  · exact le_inf (le_inf (le_trans (inf_le_left ..) (inf_le_left ..))
      (le_trans (inf_le_right ..) (inf_le_left ..)))
      (le_trans (inf_le_left ..) (inf_le_right ..))

end Simp

attribute [simp] compl_inf compl_sup le_himp_iff
end Loom.Order
