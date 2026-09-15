import Loom.Order.CompleteLattice

namespace Loom.Order

universe u v

/-- A complete distributive complemented lattice. Implication is an explicit
operation so the proposition model can reduce directly to Lean implication. -/
class CompleteBooleanAlgebra (α : Type u) extends CompleteLattice α where
  compl : α → α
  himp : α → α → α
  inf_sup_left : ∀ (a b c : α), a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c)
  inf_compl_eq_bot : ∀ a, a ⊓ compl a = bot
  sup_compl_eq_top : ∀ a, a ⊔ compl a = top
  himp_eq : ∀ a b, himp a b = compl a ⊔ b

export CompleteBooleanAlgebra (compl himp inf_sup_left inf_compl_eq_bot sup_compl_eq_top himp_eq)

attribute [scoped simp] inf_compl_eq_bot sup_compl_eq_top

variable {α : Type u} [CompleteBooleanAlgebra α] {a b c : α}

theorem inf_sup_right (a b c : α) : (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c) := by
  rw [inf_comm, inf_sup_left, inf_comm c a, inf_comm c b]

/-- Boolean implication is right adjoint to meet. -/
@[scoped simp] theorem le_himp_iff : a ≤ himp b c ↔ a ⊓ b ≤ c := by
  rw [himp_eq]
  constructor
  · intro h
    have k := inf_mono h (le_refl b)
    rw [inf_sup_right, inf_comm (compl b) b, inf_compl_eq_bot, bot_sup] at k
    exact le_trans k Std.min_le_left
  · intro h
    have k : a = (a ⊓ b) ⊔ (a ⊓ compl b) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top]
    rw [k]
    exact sup_le (le_sup_of_le_right h) (le_sup_of_le_left Std.min_le_right)

theorem le_himp_iff' : a ≤ himp b c ↔ b ⊓ a ≤ c := by
  rw [le_himp_iff, inf_comm]

theorem le_compl_iff : a ≤ compl b ↔ a ⊓ b ≤ bot := by
  have h := le_himp_iff (a := a) (b := b) (c := bot)
  simpa only [himp_eq, sup_bot] using h

theorem compl_antitone (h : a ≤ b) : compl b ≤ compl a := by
  apply le_compl_iff.mpr
  have k := inf_mono (le_refl (compl b)) h
  rw [inf_comm (compl b) b, inf_compl_eq_bot] at k
  exact k

@[scoped simp] theorem compl_compl (a : α) : compl (compl a) = a := by
  have lower : a ≤ compl (compl a) := le_compl_iff.mpr (by simp)
  have upper : compl (compl a) ≤ a := by
    have k : compl (compl a) =
        (compl (compl a) ⊓ a) ⊔ (compl (compl a) ⊓ compl a) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top]
    rw [k, inf_comm (compl (compl a)) (compl a), inf_compl_eq_bot, sup_bot]
    exact Std.min_le_right
  exact le_antisymm upper lower

@[scoped simp] theorem compl_le_compl_iff : compl a ≤ compl b ↔ b ≤ a :=
  ⟨fun h => by simpa only [compl_compl] using compl_antitone h, compl_antitone⟩

@[scoped simp] theorem compl_sup (a b : α) : compl (a ⊔ b) = compl a ⊓ compl b := by
  apply le_antisymm
  · exact le_inf (compl_antitone Std.left_le_max) (compl_antitone Std.right_le_max)
  · apply le_compl_iff.mpr
    rw [inf_sup_left]
    apply sup_le
    · exact le_trans (inf_mono Std.min_le_left (le_refl a))
        (by rw [inf_comm, inf_compl_eq_bot]; exact le_refl _)
    · exact le_trans (inf_mono Std.min_le_right (le_refl b))
        (by rw [inf_comm, inf_compl_eq_bot]; exact le_refl _)

@[scoped simp] theorem compl_inf (a b : α) : compl (a ⊓ b) = compl a ⊔ compl b := by
  have h := congrArg compl (compl_sup (compl a) (compl b))
  simpa only [compl_compl] using h.symm

@[scoped simp] theorem compl_top : compl (top : α) = bot := by
  simpa only [top_inf] using inf_compl_eq_bot (top : α)

@[scoped simp] theorem compl_bot : compl (bot : α) = top := by
  simpa only [bot_sup] using sup_compl_eq_top (bot : α)

@[scoped simp] theorem compl_inf_eq_bot (a : α) : compl a ⊓ a = bot := by
  rw [inf_comm, inf_compl_eq_bot]

@[scoped simp] theorem compl_sup_eq_top (a : α) : compl a ⊔ a = top := by
  rw [sup_comm, sup_compl_eq_top]

theorem compl_le_iff : compl a ≤ b ↔ top ≤ a ⊔ b := by
  simpa only [himp_eq, top_inf, compl_compl] using
    (le_himp_iff (a := top) (b := compl a) (c := b)).symm

theorem sup_inf_left (a b c : α) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  have h := congrArg compl (inf_sup_left (compl a) (compl b) (compl c))
  simpa only [compl_inf, compl_sup, compl_compl] using h

theorem inf_inf_distrib_right (a b c : α) : (a ⊓ b) ⊓ c = (a ⊓ c) ⊓ (b ⊓ c) := by
  rw [inf_assoc a c, ← inf_assoc c, inf_comm c b, inf_assoc b, inf_self, inf_assoc]

theorem himp_eq_sup_compl (a b : α) : himp a b = b ⊔ compl a := by
  rw [himp_eq, sup_comm]

@[scoped simp] theorem top_himp (a : α) : himp top a = a := by simp [himp_eq]
@[scoped simp] theorem bot_himp (a : α) : himp bot a = top := by simp [himp_eq]

theorem compl_iSup {ι : Sort v} (f : ι → α) :
    compl (iSup f) = iInf (fun i => compl (f i)) := by
  apply le_antisymm
  · exact le_iInf fun i => compl_antitone (le_iSup f i)
  · have h : iSup f ≤ compl (iInf (fun i => compl (f i))) := by
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
    a ⊓ iSup f = iSup (fun i => a ⊓ f i) := by
  apply le_antisymm
  · rw [inf_comm]
    apply le_himp_iff.mp
    apply iSup_le
    intro i
    apply le_himp_iff.mpr
    rw [inf_comm]
    exact le_iSup (fun i => a ⊓ f i) i
  · exact iSup_le fun i => inf_mono (le_refl a) (le_iSup f i)

theorem sup_iInf {ι : Sort v} (a : α) (f : ι → α) :
    a ⊔ iInf f = iInf (fun i => a ⊔ f i) := by
  have h := congrArg compl (inf_iSup (compl a) (fun i => compl (f i)))
  simpa only [compl_inf, compl_iSup, compl_compl] using h

end Loom.Order
