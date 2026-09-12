import Loom.Order.Defs

namespace Loom.Order

universe u v w

/-- Bounds of arbitrary predicate-defined subsets. Indexed operations below
use ranges, so their index sorts need not live in the carrier universe. -/
class CompleteLattice (α : Type u) extends Lattice α, OrderTop α, OrderBot α where
  sInf : (α → Prop) → α
  sSup : (α → Prop) → α
  sInf_le : ∀ {s a}, s a → sInf s ⊑ₗ a
  le_sInf : ∀ {s a}, (∀ b, s b → a ⊑ₗ b) → a ⊑ₗ sInf s
  le_sSup : ∀ {s a}, s a → a ⊑ₗ sSup s
  sSup_le : ∀ {s a}, (∀ b, s b → b ⊑ₗ a) → sSup s ⊑ₗ a

export CompleteLattice (sInf sSup sInf_le le_sInf le_sSup sSup_le)

variable {α : Type u} [CompleteLattice α]

def iInf {ι : Sort v} (f : ι → α) : α := sInf (fun a => ∃ i, f i = a)
def iSup {ι : Sort v} (f : ι → α) : α := sSup (fun a => ∃ i, f i = a)

theorem iInf_le {ι : Sort v} (f : ι → α) (i : ι) : iInf f ⊑ₗ f i :=
  sInf_le ⟨i, rfl⟩

theorem le_iInf {ι : Sort v} {f : ι → α} {a : α}
    (h : ∀ i, a ⊑ₗ f i) : a ⊑ₗ iInf f :=
  le_sInf fun _ ⟨i, hi⟩ => hi ▸ h i

theorem le_iSup {ι : Sort v} (f : ι → α) (i : ι) : f i ⊑ₗ iSup f :=
  le_sSup ⟨i, rfl⟩

theorem iSup_le {ι : Sort v} {f : ι → α} {a : α}
    (h : ∀ i, f i ⊑ₗ a) : iSup f ⊑ₗ a :=
  sSup_le fun _ ⟨i, hi⟩ => hi ▸ h i

@[simp] theorem le_iInf_iff {ι : Sort v} {f : ι → α} {a : α} :
    a ⊑ₗ iInf f ↔ ∀ i, a ⊑ₗ f i :=
  ⟨fun h i => le_trans h (iInf_le f i), le_iInf⟩

@[simp] theorem iSup_le_iff {ι : Sort v} {f : ι → α} {a : α} :
    iSup f ⊑ₗ a ↔ ∀ i, f i ⊑ₗ a :=
  ⟨fun h i => le_trans (le_iSup f i) h, iSup_le⟩

theorem iInf_le_of_le {ι : Sort v} {f : ι → α} (i : ι) {a : α}
    (h : f i ⊑ₗ a) : iInf f ⊑ₗ a := le_trans (iInf_le f i) h

theorem le_iSup_of_le {ι : Sort v} {f : ι → α} (i : ι) {a : α}
    (h : a ⊑ₗ f i) : a ⊑ₗ iSup f := le_trans h (le_iSup f i)

theorem iInf_mono {ι : Sort v} {f g : ι → α} (h : ∀ i, f i ⊑ₗ g i) :
    iInf f ⊑ₗ iInf g := le_iInf fun i => iInf_le_of_le (f := f) i (h i)

theorem iSup_mono {ι : Sort v} {f g : ι → α} (h : ∀ i, f i ⊑ₗ g i) :
    iSup f ⊑ₗ iSup g := iSup_le fun i => le_iSup_of_le (f := g) i (h i)

theorem iInf_congr {ι : Sort v} {f g : ι → α} (h : ∀ i, f i = g i) :
    iInf f = iInf g := congrArg iInf (funext h)

theorem iSup_congr {ι : Sort v} {f g : ι → α} (h : ∀ i, f i = g i) :
    iSup f = iSup g := congrArg iSup (funext h)

/-- Congruence for proposition indices lets simplification rewrite bounded
quantifier domains, including list membership and assumptions. -/
theorem iInf_congr_prop {p q : Prop} {f : p → α} {g : q → α}
    (hpq : p ↔ q) (h : ∀ hq, f (hpq.mpr hq) = g hq) : iInf f = iInf g := by
  obtain rfl := propext hpq
  exact iInf_congr h

theorem iSup_congr_prop {p q : Prop} {f : p → α} {g : q → α}
    (hpq : p ↔ q) (h : ∀ hq, f (hpq.mpr hq) = g hq) : iSup f = iSup g := by
  obtain rfl := propext hpq
  exact iSup_congr h

theorem le_iInf₂ {ι : Sort v} {κ : ι → Sort w} {f : (i : ι) → κ i → α} {a : α}
    (h : ∀ i j, a ⊑ₗ f i j) : a ⊑ₗ iInf (fun i => iInf (f i)) :=
  le_iInf fun i => le_iInf (h i)

theorem iSup_le₂ {ι : Sort v} {κ : ι → Sort w} {f : (i : ι) → κ i → α} {a : α}
    (h : ∀ i j, f i j ⊑ₗ a) : iSup (fun i => iSup (f i)) ⊑ₗ a :=
  iSup_le fun i => iSup_le (h i)

@[simp] theorem iInf_top {ι : Sort v} : iInf (fun (_ : ι) => (top : α)) = top :=
  le_antisymm (le_top _) (le_iInf fun _ => le_refl _)

@[simp] theorem iSup_bot {ι : Sort v} : iSup (fun (_ : ι) => (bot : α)) = bot :=
  le_antisymm (iSup_le fun _ => le_refl _) (bot_le _)

@[simp] theorem iInf_const {ι : Sort v} [Nonempty ι] (a : α) :
    iInf (fun (_ : ι) => a) = a := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact le_antisymm (iInf_le _ i) (le_iInf fun _ => le_refl _)

@[simp] theorem iSup_const {ι : Sort v} [Nonempty ι] (a : α) :
    iSup (fun (_ : ι) => a) = a := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact le_antisymm (iSup_le fun _ => le_refl _) (le_iSup (fun (_ : ι) => a) i)

theorem iInf_of_empty {ι : Sort v} (empty : ι → False) (f : ι → α) : iInf f = top :=
  le_antisymm (le_top _) (le_iInf fun i => (empty i).elim)

theorem iSup_of_empty {ι : Sort v} (empty : ι → False) (f : ι → α) : iSup f = bot :=
  le_antisymm (iSup_le fun i => (empty i).elim) (bot_le _)

@[simp] theorem iInf_bool_eq (f : Bool → α) : iInf f = f false ⊓ₗ f true := by
  apply le_antisymm
  · exact le_inf (iInf_le f false) (iInf_le f true)
  · exact le_iInf fun b => by cases b; exact inf_le_left ..; exact inf_le_right ..

@[simp] theorem iSup_bool_eq (f : Bool → α) : iSup f = f false ⊔ₗ f true := by
  apply le_antisymm
  · exact iSup_le fun b => by cases b; exact le_sup_left ..; exact le_sup_right ..
  · exact sup_le (le_iSup f false) (le_iSup f true)

@[simp] theorem iInf_ulift {ι : Type v} (f : ULift.{w} ι → α) :
    iInf f = iInf (fun i => f (.up i)) := by
  apply le_antisymm
  · exact le_iInf fun i => iInf_le f (.up i)
  · exact le_iInf fun ⟨i⟩ => iInf_le (fun i => f (.up i)) i

@[simp] theorem iSup_ulift {ι : Type v} (f : ULift.{w} ι → α) :
    iSup f = iSup (fun i => f (.up i)) := by
  apply le_antisymm
  · exact iSup_le fun ⟨i⟩ => le_iSup (fun i => f (.up i)) i
  · exact iSup_le fun i => le_iSup f (.up i)

@[simp] theorem iInf_of_pos {p : Prop} (hp : p) (f : p → α) : iInf f = f hp :=
  le_antisymm (iInf_le f hp) (le_iInf fun _ => le_refl _)

@[simp] theorem iSup_of_pos {p : Prop} (hp : p) (f : p → α) : iSup f = f hp :=
  le_antisymm (iSup_le fun _ => le_refl _) (le_iSup f hp)

@[simp] theorem iInf_of_neg {p : Prop} (hp : ¬p) (f : p → α) : iInf f = top :=
  iInf_of_empty hp f

@[simp] theorem iSup_of_neg {p : Prop} (hp : ¬p) (f : p → α) : iSup f = bot :=
  iSup_of_empty hp f

@[simp] theorem iInf_punit (f : PUnit.{v} → α) : iInf f = f .unit :=
  le_antisymm (iInf_le f .unit) (le_iInf fun ⟨⟩ => le_refl _)

@[simp] theorem iSup_punit (f : PUnit.{v} → α) : iSup f = f .unit :=
  le_antisymm (iSup_le fun ⟨⟩ => le_refl _) (le_iSup f .unit)

@[simp] theorem iSup_eq {ι : Sort v} (b : ι) (f : ι → α) :
    iSup (fun a => iSup (fun (_ : a = b) => f a)) = f b := by
  apply le_antisymm
  · exact iSup_le fun a => iSup_le fun h => h ▸ le_refl _
  · exact le_iSup_of_le b (le_iSup_of_le rfl (le_refl _))

@[simp] theorem iSup_eq' {ι : Sort v} (b : ι) (f : ι → α) :
    iSup (fun a => iSup (fun (_ : b = a) => f a)) = f b := by
  apply le_antisymm
  · exact iSup_le fun a => iSup_le fun h => h ▸ le_refl _
  · exact le_iSup_of_le b (le_iSup_of_le rfl (le_refl _))

theorem iSup_or (p q : Prop) (f : p ∨ q → α) :
    iSup f = iSup (fun hp => f (.inl hp)) ⊔ₗ iSup (fun hq => f (.inr hq)) := by
  apply le_antisymm
  · apply iSup_le
    intro h
    cases h with
    | inl hp => exact le_sup_of_le_left (le_iSup (fun hp => f (.inl hp)) hp)
    | inr hq => exact le_sup_of_le_right (le_iSup (fun hq => f (.inr hq)) hq)
  · exact sup_le (iSup_le fun hp => le_iSup f (.inl hp))
      (iSup_le fun hq => le_iSup f (.inr hq))

theorem iSup_sup_eq {ι : Sort v} (f g : ι → α) :
    iSup (fun i => f i ⊔ₗ g i) = iSup f ⊔ₗ iSup g := by
  apply le_antisymm
  · exact iSup_le fun i => sup_mono (le_iSup f i) (le_iSup g i)
  · exact sup_le
      (iSup_le fun i => le_iSup_of_le i (le_sup_left (f i) (g i)))
      (iSup_le fun i => le_iSup_of_le i (le_sup_right (f i) (g i)))

theorem iInf_comm {ι : Sort v} {κ : Sort w} (f : ι → κ → α) :
    iInf (fun i => iInf (f i)) = iInf (fun j => iInf (fun i => f i j)) := by
  apply le_antisymm
  · exact le_iInf fun j => le_iInf fun i => le_trans (iInf_le _ i) (iInf_le _ j)
  · exact le_iInf fun i => le_iInf fun j => le_trans (iInf_le _ j) (iInf_le _ i)

theorem iSup_comm {ι : Sort v} {κ : Sort w} (f : ι → κ → α) :
    iSup (fun i => iSup (f i)) = iSup (fun j => iSup (fun i => f i j)) := by
  apply le_antisymm
  · exact iSup_le fun i => iSup_le fun j => le_trans (le_iSup (fun i => f i j) i) (le_iSup (fun j => iSup (fun i => f i j)) j)
  · exact iSup_le fun j => iSup_le fun i => le_trans (le_iSup (f i) j) (le_iSup (fun i => iSup (f i)) i)

end Loom.Order
