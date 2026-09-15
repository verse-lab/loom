module

public import Loom.Order.Defs

@[expose] public section

namespace Loom.Order

universe u v w

/-- Explicit bound operations keep concrete models such as `Prop` definitionally reducible. -/
class CompleteLattice (α : Type u) extends LE α, Min α, Max α,
    Std.IsPartialOrder α, Std.LawfulOrderInf α, Std.LawfulOrderSup α where
  top : α
  bot : α
  le_top : ∀ a : α, a ≤ top
  bot_le : ∀ a : α, bot ≤ a
  sInf : (α → Prop) → α
  sSup : (α → Prop) → α
  sInf_le : ∀ {s a}, s a → sInf s ≤ a
  le_sInf : ∀ {s a}, (∀ b, s b → a ≤ b) → a ≤ sInf s
  le_sSup : ∀ {s a}, s a → a ≤ sSup s
  sSup_le : ∀ {s a}, (∀ b, s b → b ≤ a) → sSup s ≤ a

export CompleteLattice (top bot le_top bot_le sInf sSup sInf_le le_sInf le_sSup sSup_le)

attribute [scoped simp] le_top bot_le

variable {α : Type u} [CompleteLattice α]

section Bounds
variable {a : α}

@[scoped simp] theorem top_le_iff : top ≤ a ↔ a = top :=
  ⟨fun h => le_antisymm (le_top _) h, fun h => h ▸ le_refl _⟩

@[scoped simp] theorem le_bot_iff : a ≤ bot ↔ a = bot :=
  ⟨fun h => le_antisymm h (bot_le _), fun h => h ▸ le_refl _⟩

theorem eq_top_iff : a = top ↔ top ≤ a := top_le_iff.symm
theorem eq_bot_iff : a = bot ↔ a ≤ bot := le_bot_iff.symm

@[scoped simp] theorem inf_top (a : α) : a ⊓ top = a :=
  le_antisymm Std.min_le_left (le_inf (le_refl _) (le_top _))

@[scoped simp] theorem top_inf (a : α) : top ⊓ a = a := by
  rw [inf_comm, inf_top]

@[scoped simp] theorem sup_bot (a : α) : a ⊔ bot = a :=
  le_antisymm (sup_le (le_refl _) (bot_le _)) Std.left_le_max

@[scoped simp] theorem bot_sup (a : α) : bot ⊔ a = a := by
  rw [sup_comm, sup_bot]

@[scoped simp] theorem inf_bot (a : α) : a ⊓ bot = bot :=
  le_antisymm Std.min_le_right (bot_le _)

@[scoped simp] theorem bot_inf (a : α) : bot ⊓ a = bot := by
  rw [inf_comm, inf_bot]

@[scoped simp] theorem sup_top (a : α) : a ⊔ top = top :=
  le_antisymm (le_top _) Std.right_le_max

@[scoped simp] theorem top_sup (a : α) : top ⊔ a = top := by
  rw [sup_comm, sup_top]

end Bounds

def iInf {ι : Sort v} (f : ι → α) : α := sInf (fun a => ∃ i, f i = a)
def iSup {ι : Sort v} (f : ι → α) : α := sSup (fun a => ∃ i, f i = a)

theorem iInf_le {ι : Sort v} (f : ι → α) (i : ι) : iInf f ≤ f i :=
  sInf_le ⟨i, rfl⟩

theorem le_iInf {ι : Sort v} {f : ι → α} {a : α}
    (h : ∀ i, a ≤ f i) : a ≤ iInf f :=
  le_sInf fun _ ⟨i, hi⟩ => hi ▸ h i

theorem le_iSup {ι : Sort v} (f : ι → α) (i : ι) : f i ≤ iSup f :=
  le_sSup ⟨i, rfl⟩

theorem iSup_le {ι : Sort v} {f : ι → α} {a : α}
    (h : ∀ i, f i ≤ a) : iSup f ≤ a :=
  sSup_le fun _ ⟨i, hi⟩ => hi ▸ h i

@[scoped simp] theorem le_iInf_iff {ι : Sort v} {f : ι → α} {a : α} :
    a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  ⟨fun h i => le_trans h (iInf_le f i), le_iInf⟩

@[scoped simp] theorem iSup_le_iff {ι : Sort v} {f : ι → α} {a : α} :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  ⟨fun h i => le_trans (le_iSup f i) h, iSup_le⟩

theorem iInf_le_of_le {ι : Sort v} {f : ι → α} (i : ι) {a : α}
    (h : f i ≤ a) : iInf f ≤ a := le_trans (iInf_le f i) h

theorem le_iSup_of_le {ι : Sort v} {f : ι → α} (i : ι) {a : α}
    (h : a ≤ f i) : a ≤ iSup f := le_trans h (le_iSup f i)

theorem iInf_mono {ι : Sort v} {f g : ι → α} (h : ∀ i, f i ≤ g i) :
    iInf f ≤ iInf g := le_iInf fun i => iInf_le_of_le i (h i)

theorem iSup_mono {ι : Sort v} {f g : ι → α} (h : ∀ i, f i ≤ g i) :
    iSup f ≤ iSup g := iSup_le fun i => le_iSup_of_le i (h i)

theorem iInf_congr {ι : Sort v} {f g : ι → α} (h : ∀ i, f i = g i) :
    iInf f = iInf g := congrArg iInf (funext h)

theorem iSup_congr {ι : Sort v} {f g : ι → α} (h : ∀ i, f i = g i) :
    iSup f = iSup g := congrArg iSup (funext h)

@[scoped congr] theorem iInf_congr_prop {p q : Prop} {f : p → α} {g : q → α}
    (hpq : p ↔ q) (h : ∀ hq, f (hpq.mpr hq) = g hq) : iInf f = iInf g := by
  obtain rfl := propext hpq
  exact iInf_congr h

@[scoped congr] theorem iSup_congr_prop {p q : Prop} {f : p → α} {g : q → α}
    (hpq : p ↔ q) (h : ∀ hq, f (hpq.mpr hq) = g hq) : iSup f = iSup g := by
  obtain rfl := propext hpq
  exact iSup_congr h

@[scoped simp] theorem iInf_top {ι : Sort v} : iInf (fun (_ : ι) => (top : α)) = top :=
  le_antisymm (le_top _) (le_iInf fun _ => le_refl _)

@[scoped simp] theorem iSup_bot {ι : Sort v} : iSup (fun (_ : ι) => (bot : α)) = bot :=
  le_antisymm (iSup_le fun _ => le_refl _) (bot_le _)

@[scoped simp] theorem iInf_const {ι : Sort v} [Nonempty ι] (a : α) :
    iInf (fun (_ : ι) => a) = a := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact le_antisymm (iInf_le _ i) (le_iInf fun _ => le_refl _)

@[scoped simp] theorem iSup_const {ι : Sort v} [Nonempty ι] (a : α) :
    iSup (fun (_ : ι) => a) = a := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact le_antisymm (iSup_le fun _ => le_refl _) (le_iSup (fun (_ : ι) => a) i)

theorem iInf_of_empty {ι : Sort v} (empty : ι → False) (f : ι → α) : iInf f = top :=
  le_antisymm (le_top _) (le_iInf fun i => (empty i).elim)

theorem iSup_of_empty {ι : Sort v} (empty : ι → False) (f : ι → α) : iSup f = bot :=
  le_antisymm (iSup_le fun i => (empty i).elim) (bot_le _)

@[scoped simp] theorem iInf_of_pos {p : Prop} (hp : p) (f : p → α) : iInf f = f hp :=
  le_antisymm (iInf_le f hp) (le_iInf fun _ => le_refl _)

@[scoped simp] theorem iSup_of_pos {p : Prop} (hp : p) (f : p → α) : iSup f = f hp :=
  le_antisymm (iSup_le fun _ => le_refl _) (le_iSup f hp)

@[scoped simp] theorem iInf_of_neg {p : Prop} (hp : ¬p) (f : p → α) : iInf f = top :=
  iInf_of_empty hp f

@[scoped simp] theorem iSup_of_neg {p : Prop} (hp : ¬p) (f : p → α) : iSup f = bot :=
  iSup_of_empty hp f

@[scoped simp] theorem iInf_bool_eq (f : Bool → α) : iInf f = f false ⊓ f true := by
  apply le_antisymm
  · exact le_inf (iInf_le f false) (iInf_le f true)
  · exact le_iInf fun b => by cases b; exact Std.min_le_left; exact Std.min_le_right

@[scoped simp] theorem iSup_bool_eq (f : Bool → α) : iSup f = f false ⊔ f true := by
  apply le_antisymm
  · exact iSup_le fun b => by cases b; exact Std.left_le_max; exact Std.right_le_max
  · exact sup_le (le_iSup f false) (le_iSup f true)

@[scoped simp] theorem iInf_ulift {ι : Type v} (f : ULift.{w} ι → α) :
    iInf f = iInf (fun i => f (.up i)) := by
  apply le_antisymm
  · exact le_iInf fun i => iInf_le f (.up i)
  · exact le_iInf fun ⟨i⟩ => iInf_le (fun i => f (.up i)) i

@[scoped simp] theorem iSup_ulift {ι : Type v} (f : ULift.{w} ι → α) :
    iSup f = iSup (fun i => f (.up i)) := by
  apply le_antisymm
  · exact iSup_le fun ⟨i⟩ => le_iSup (fun i => f (.up i)) i
  · exact iSup_le fun i => le_iSup f (.up i)

@[scoped simp] theorem iSup_punit (f : PUnit.{v} → α) : iSup f = f .unit :=
  le_antisymm (iSup_le fun ⟨⟩ => le_refl _) (le_iSup f .unit)

@[scoped simp] theorem iSup_eq {ι : Sort v} (b : ι) (f : ι → α) :
    iSup (fun a => iSup (fun (_ : a = b) => f a)) = f b := by
  apply le_antisymm
  · exact iSup_le fun a => iSup_le fun h => h ▸ le_refl _
  · exact le_iSup_of_le b (le_iSup_of_le rfl (le_refl _))

theorem iSup_or (p q : Prop) (f : p ∨ q → α) :
    iSup f = iSup (fun hp => f (.inl hp)) ⊔ iSup (fun hq => f (.inr hq)) := by
  apply le_antisymm
  · apply iSup_le
    intro h
    cases h with
    | inl hp => exact le_sup_of_le_left (le_iSup (fun hp => f (.inl hp)) hp)
    | inr hq => exact le_sup_of_le_right (le_iSup (fun hq => f (.inr hq)) hq)
  · exact sup_le (iSup_le fun hp => le_iSup f (.inl hp))
      (iSup_le fun hq => le_iSup f (.inr hq))

theorem iSup_sup_eq {ι : Sort v} (f g : ι → α) :
    iSup (fun i => f i ⊔ g i) = iSup f ⊔ iSup g := by
  apply le_antisymm
  · exact iSup_le fun i => sup_mono (le_iSup f i) (le_iSup g i)
  · exact sup_le
      (iSup_le fun i => le_iSup_of_le i Std.left_le_max)
      (iSup_le fun i => le_iSup_of_le i Std.right_le_max)

theorem iInf_comm {ι : Sort v} {κ : Sort w} (f : ι → κ → α) :
    iInf (fun i => iInf (f i)) = iInf (fun j => iInf (fun i => f i j)) := by
  apply le_antisymm
  · exact le_iInf fun j => le_iInf fun i => le_trans (iInf_le _ i) (iInf_le _ j)
  · exact le_iInf fun i => le_iInf fun j => le_trans (iInf_le _ j) (iInf_le _ i)

end Loom.Order
