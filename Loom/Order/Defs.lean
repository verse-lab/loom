import Init

/-! Assertion order, independent of both mathlib's `LE` and Lean's CCPO order. -/

namespace Loom.Order

universe u

class Preorder (α : Type u) where
  le : α → α → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c

scoped infix:50 " ⊑ₗ " => Preorder.le

class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ {a b : α}, a ⊑ₗ b → b ⊑ₗ a → a = b

class OrderTop (α : Type u) [Preorder α] where
  top : α
  le_top : ∀ a, a ⊑ₗ top

class OrderBot (α : Type u) [Preorder α] where
  bot : α
  bot_le : ∀ a, bot ⊑ₗ a

class Lattice (α : Type u) extends PartialOrder α where
  inf : α → α → α
  sup : α → α → α
  inf_le_left : ∀ a b, inf a b ⊑ₗ a
  inf_le_right : ∀ a b, inf a b ⊑ₗ b
  le_inf : ∀ {a b c : α}, a ⊑ₗ b → a ⊑ₗ c → a ⊑ₗ inf b c
  le_sup_left : ∀ a b, a ⊑ₗ sup a b
  le_sup_right : ∀ a b, b ⊑ₗ sup a b
  sup_le : ∀ {a b c : α}, a ⊑ₗ c → b ⊑ₗ c → sup a b ⊑ₗ c

export Preorder (le_refl le_trans)
export PartialOrder (le_antisymm)
export OrderTop (top le_top)
export OrderBot (bot bot_le)
export Lattice (inf sup inf_le_left inf_le_right le_inf le_sup_left le_sup_right sup_le)

scoped infixl:70 " ⊓ₗ " => inf
scoped infixl:65 " ⊔ₗ " => sup

attribute [simp] le_refl le_top bot_le
attribute [simp] inf_le_left inf_le_right le_sup_left le_sup_right

variable {α : Type u}

def ge [Preorder α] (a b : α) : Prop := b ⊑ₗ a

@[simp] theorem ge_iff_le [Preorder α] {a b : α} : ge a b ↔ b ⊑ₗ a := Iff.rfl

theorem ge_refl [Preorder α] (a : α) : ge a a := le_refl a

theorem le_trans' [Preorder α] {a b c : α} (h : b ⊑ₗ c) (k : a ⊑ₗ b) : a ⊑ₗ c :=
  le_trans k h

theorem le_of_eq [Preorder α] {a b : α} (h : a = b) : a ⊑ₗ b := h ▸ le_refl a

def Monotone [Preorder α] [Preorder β] (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ⊑ₗ b → f a ⊑ₗ f b

@[simp] theorem top_le_iff [PartialOrder α] [OrderTop α] {a : α} :
    top ⊑ₗ a ↔ a = top :=
  ⟨fun h => le_antisymm (le_top _) h, fun h => h ▸ le_refl _⟩

@[simp] theorem le_bot_iff [PartialOrder α] [OrderBot α] {a : α} :
    a ⊑ₗ bot ↔ a = bot :=
  ⟨fun h => le_antisymm h (bot_le _), fun h => h ▸ le_refl _⟩

theorem eq_bot_iff [PartialOrder α] [OrderBot α] {a : α} :
    a = bot ↔ a ⊑ₗ bot := le_bot_iff.symm

section
variable [Lattice α] {a b c d : α}

@[simp] theorem le_inf_iff : a ⊑ₗ b ⊓ₗ c ↔ a ⊑ₗ b ∧ a ⊑ₗ c :=
  ⟨fun h => ⟨le_trans h (inf_le_left ..), le_trans h (inf_le_right ..)⟩,
    fun h => le_inf h.1 h.2⟩

@[simp] theorem sup_le_iff : a ⊔ₗ b ⊑ₗ c ↔ a ⊑ₗ c ∧ b ⊑ₗ c :=
  ⟨fun h => ⟨le_trans (le_sup_left ..) h, le_trans (le_sup_right ..) h⟩,
    fun h => sup_le h.1 h.2⟩

theorem inf_mono (h : a ⊑ₗ b) (k : c ⊑ₗ d) : a ⊓ₗ c ⊑ₗ b ⊓ₗ d :=
  le_inf (le_trans (inf_le_left ..) h) (le_trans (inf_le_right ..) k)

theorem sup_mono (h : a ⊑ₗ b) (k : c ⊑ₗ d) : a ⊔ₗ c ⊑ₗ b ⊔ₗ d :=
  sup_le (le_trans h (le_sup_left ..)) (le_trans k (le_sup_right ..))

theorem inf_le_of_left_le (h : a ⊑ₗ c) : a ⊓ₗ b ⊑ₗ c := le_trans (inf_le_left ..) h
theorem inf_le_of_right_le (h : b ⊑ₗ c) : a ⊓ₗ b ⊑ₗ c := le_trans (inf_le_right ..) h
theorem le_sup_of_le_left (h : a ⊑ₗ b) : a ⊑ₗ b ⊔ₗ c := le_trans h (le_sup_left ..)
theorem le_sup_of_le_right (h : a ⊑ₗ c) : a ⊑ₗ b ⊔ₗ c := le_trans h (le_sup_right ..)

@[simp] theorem inf_le_sup_ll (a b c : α) : a ⊓ₗ b ⊑ₗ a ⊔ₗ c :=
  le_trans (inf_le_left ..) (le_sup_left ..)
@[simp] theorem inf_le_sup_lr (a b c : α) : a ⊓ₗ b ⊑ₗ c ⊔ₗ a :=
  le_trans (inf_le_left ..) (le_sup_right ..)
@[simp] theorem inf_le_sup_rl (a b c : α) : a ⊓ₗ b ⊑ₗ b ⊔ₗ c :=
  le_trans (inf_le_right ..) (le_sup_left ..)
@[simp] theorem inf_le_sup_rr (a b c : α) : a ⊓ₗ b ⊑ₗ c ⊔ₗ b :=
  le_trans (inf_le_right ..) (le_sup_right ..)

theorem inf_comm (a b : α) : a ⊓ₗ b = b ⊓ₗ a :=
  le_antisymm (le_inf (inf_le_right ..) (inf_le_left ..))
    (le_inf (inf_le_right ..) (inf_le_left ..))

theorem sup_comm (a b : α) : a ⊔ₗ b = b ⊔ₗ a :=
  le_antisymm (sup_le (le_sup_right ..) (le_sup_left ..))
    (sup_le (le_sup_right ..) (le_sup_left ..))

theorem inf_assoc (a b c : α) : (a ⊓ₗ b) ⊓ₗ c = a ⊓ₗ (b ⊓ₗ c) := by
  apply le_antisymm
  · exact le_inf (le_trans (inf_le_left ..) (inf_le_left ..))
      (le_inf (le_trans (inf_le_left ..) (inf_le_right ..)) (inf_le_right ..))
  · exact le_inf (le_inf (inf_le_left ..) (le_trans (inf_le_right ..) (inf_le_left ..)))
      (le_trans (inf_le_right ..) (inf_le_right ..))

theorem sup_assoc (a b c : α) : (a ⊔ₗ b) ⊔ₗ c = a ⊔ₗ (b ⊔ₗ c) := by
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left ..) (le_trans (le_sup_left ..) (le_sup_right ..)))
      (le_trans (le_sup_right ..) (le_sup_right ..))
  · exact sup_le (le_trans (le_sup_left ..) (le_sup_left ..))
      (sup_le (le_trans (le_sup_right ..) (le_sup_left ..)) (le_sup_right ..))

@[simp] theorem inf_self (a : α) : a ⊓ₗ a = a :=
  le_antisymm (inf_le_left ..) (le_inf (le_refl _) (le_refl _))

@[simp] theorem sup_self (a : α) : a ⊔ₗ a = a :=
  le_antisymm (sup_le (le_refl _) (le_refl _)) (le_sup_left ..)

@[simp] theorem inf_top [OrderTop α] (a : α) : a ⊓ₗ top = a :=
  le_antisymm (inf_le_left ..) (le_inf (le_refl _) (le_top _))

@[simp] theorem top_inf [OrderTop α] (a : α) : top ⊓ₗ a = a := by
  rw [inf_comm, inf_top]

@[simp] theorem sup_bot [OrderBot α] (a : α) : a ⊔ₗ bot = a :=
  le_antisymm (sup_le (le_refl _) (bot_le _)) (le_sup_left ..)

@[simp] theorem bot_sup [OrderBot α] (a : α) : bot ⊔ₗ a = a := by
  rw [sup_comm, sup_bot]

@[simp] theorem inf_bot [OrderBot α] (a : α) : a ⊓ₗ bot = bot :=
  le_antisymm (inf_le_right ..) (bot_le _)

@[simp] theorem bot_inf [OrderBot α] (a : α) : bot ⊓ₗ a = bot := by
  rw [inf_comm, inf_bot]

@[simp] theorem sup_top [OrderTop α] (a : α) : a ⊔ₗ top = top :=
  le_antisymm (le_top _) (le_sup_right ..)

@[simp] theorem top_sup [OrderTop α] (a : α) : top ⊔ₗ a = top := by
  rw [sup_comm, sup_top]

end
end Loom.Order
