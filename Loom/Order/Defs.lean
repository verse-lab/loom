import Init.Data.Order.Lemmas

/-! Assertion order, independent of both mathlib's `LE` and Lean's CCPO order. -/

namespace Loom.Order

universe u

/-- An assertion relation, without reflexivity or transitivity assumptions.
This separate operation dictionary allows assertion and numeric/mathlib orders
on the same type; the order laws themselves are supplied by `Std`. -/
class LE (α : Type u) where
  le : α → α → Prop

-- Resolve familiar comparison syntax without changing either underlying LE.
-- Both the selector and its instances reduce before arithmetic/proof tactics.
private class NotationLE (α : Type u) where
  le : α → α → Prop

attribute [reducible] NotationLE.le

@[reducible]
scoped instance (priority := high) [LE α] : NotationLE α := ⟨LE.le⟩
@[reducible]
scoped instance (priority := low) [h : _root_.LE α] : NotationLE α := ⟨h.le⟩

-- The first spelling also supplies the pretty-printer for the bare relation.
scoped infix:50 (priority := high) unicode(" ≤ ", " <= ") => LE.le

/-- Bundle the assertion relation with the standard preorder laws. The explicit
`LE` argument keeps these laws independent of an ambient numeric/mathlib order. -/
class Preorder (α : Type u) extends LE α, @Std.IsPreorder α ⟨le⟩

-- Keep the previous qualified spelling available after moving the field to LE.
namespace Preorder
export LE (le)
end Preorder

class PartialOrder (α : Type u) extends Preorder α, @Std.IsPartialOrder α ⟨le⟩

class OrderTop (α : Type u) [LE α] where
  top : α
  le_top : ∀ a, a ≤ top

class OrderBot (α : Type u) [LE α] where
  bot : α
  bot_le : ∀ a, bot ≤ a

/-- A lattice uses the standard operations and their universal-property laws.
The operations are accessed explicitly, so importing Loom never installs a
numeric/mathlib `Min` or `Max` instance. -/
class Lattice (α : Type u) extends PartialOrder α, Min α, Max α,
    @Std.LawfulOrderInf α toMin ⟨le⟩, @Std.LawfulOrderSup α toMax ⟨le⟩

attribute [-instance] Lattice.toMin Lattice.toMax

namespace Lattice
def inf [self : Lattice α] : α → α → α := self.toMin.min
def sup [self : Lattice α] : α → α → α := self.toMax.max
end Lattice

-- Retain Loom's implicit-argument theorem interface over the standard laws.
theorem le_refl [Preorder α] (a : α) : a ≤ a :=
  @Std.IsPreorder.le_refl α ⟨LE.le⟩ _ a

theorem le_trans [Preorder α] {a b c : α} (h : a ≤ b) (k : b ≤ c) : a ≤ c :=
  @Std.IsPreorder.le_trans α ⟨LE.le⟩ _ a b c h k

theorem le_antisymm [PartialOrder α] {a b : α} (h : a ≤ b) (k : b ≤ a) : a = b :=
  @Std.IsPartialOrder.le_antisymm α ⟨LE.le⟩ _ a b h k

export OrderTop (top le_top)
export OrderBot (bot bot_le)
export Lattice (inf sup)

scoped infixl:70 (priority := high) " ⊓ " => inf
scoped infixl:65 (priority := high) " ⊔ " => sup

section StandardLattice
variable [Lattice α]
local instance : _root_.LE α := ⟨LE.le⟩
local instance : Min α := Lattice.toMin
local instance : Max α := Lattice.toMax

@[simp] theorem le_inf_iff {a b c : α} : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
  Std.le_min_iff (α := α)

@[simp] theorem sup_le_iff {a b c : α} : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  Std.max_le_iff (α := α)

theorem inf_le_left (a b : α) : a ⊓ b ≤ a := Std.min_le_left (α := α)
theorem inf_le_right (a b : α) : a ⊓ b ≤ b := Std.min_le_right (α := α)
theorem le_inf {a b c : α} (h : a ≤ b) (k : a ≤ c) : a ≤ b ⊓ c :=
  (Std.le_min_iff (α := α)).mpr ⟨h, k⟩
theorem le_sup_left (a b : α) : a ≤ a ⊔ b := Std.left_le_max (α := α)
theorem le_sup_right (a b : α) : b ≤ a ⊔ b := Std.right_le_max (α := α)
theorem sup_le {a b c : α} (h : a ≤ c) (k : b ≤ c) : a ⊔ b ≤ c :=
  (Std.max_le_iff (α := α)).mpr ⟨h, k⟩
end StandardLattice

attribute [simp] le_refl le_top bot_le
attribute [simp] inf_le_left inf_le_right le_sup_left le_sup_right

variable {α : Type u}

def ge [Preorder α] (a b : α) : Prop := b ≤ a

@[simp] theorem ge_iff_le [Preorder α] {a b : α} : ge a b ↔ b ≤ a := Iff.rfl

theorem ge_refl [Preorder α] (a : α) : ge a a := le_refl a

theorem le_trans' [Preorder α] {a b c : α} (h : b ≤ c) (k : a ≤ b) : a ≤ c :=
  le_trans k h

theorem le_of_eq [Preorder α] {a b : α} (h : a = b) : a ≤ b :=
  @Std.le_of_eq α ⟨LE.le⟩ _ a b h

def Monotone [Preorder α] [Preorder β] (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

@[simp] theorem top_le_iff [PartialOrder α] [OrderTop α] {a : α} :
    top ≤ a ↔ a = top :=
  ⟨fun h => le_antisymm (le_top _) h, fun h => h ▸ le_refl _⟩

@[simp] theorem le_bot_iff [PartialOrder α] [OrderBot α] {a : α} :
    a ≤ bot ↔ a = bot :=
  ⟨fun h => le_antisymm h (bot_le _), fun h => h ▸ le_refl _⟩

theorem eq_bot_iff [PartialOrder α] [OrderBot α] {a : α} :
    a = bot ↔ a ≤ bot := le_bot_iff.symm

section
variable [Lattice α] {a b c d : α}

theorem inf_mono (h : a ≤ b) (k : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
  le_inf (le_trans (inf_le_left ..) h) (le_trans (inf_le_right ..) k)

theorem sup_mono (h : a ≤ b) (k : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
  sup_le (le_trans h (le_sup_left ..)) (le_trans k (le_sup_right ..))

theorem inf_le_of_left_le (h : a ≤ c) : a ⊓ b ≤ c := le_trans (inf_le_left ..) h
theorem inf_le_of_right_le (h : b ≤ c) : a ⊓ b ≤ c := le_trans (inf_le_right ..) h
theorem le_sup_of_le_left (h : a ≤ b) : a ≤ b ⊔ c := le_trans h (le_sup_left ..)
theorem le_sup_of_le_right (h : a ≤ c) : a ≤ b ⊔ c := le_trans h (le_sup_right ..)

@[simp] theorem inf_le_sup_ll (a b c : α) : a ⊓ b ≤ a ⊔ c :=
  le_trans (inf_le_left ..) (le_sup_left ..)
@[simp] theorem inf_le_sup_lr (a b c : α) : a ⊓ b ≤ c ⊔ a :=
  le_trans (inf_le_left ..) (le_sup_right ..)
@[simp] theorem inf_le_sup_rl (a b c : α) : a ⊓ b ≤ b ⊔ c :=
  le_trans (inf_le_right ..) (le_sup_left ..)
@[simp] theorem inf_le_sup_rr (a b c : α) : a ⊓ b ≤ c ⊔ b :=
  le_trans (inf_le_right ..) (le_sup_right ..)

theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a :=
  le_antisymm (le_inf (inf_le_right ..) (inf_le_left ..))
    (le_inf (inf_le_right ..) (inf_le_left ..))

theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a :=
  le_antisymm (sup_le (le_sup_right ..) (le_sup_left ..))
    (sup_le (le_sup_right ..) (le_sup_left ..))

theorem inf_assoc (a b c : α) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) := by
  apply le_antisymm
  · exact le_inf (le_trans (inf_le_left ..) (inf_le_left ..))
      (le_inf (le_trans (inf_le_left ..) (inf_le_right ..)) (inf_le_right ..))
  · exact le_inf (le_inf (inf_le_left ..) (le_trans (inf_le_right ..) (inf_le_left ..)))
      (le_trans (inf_le_right ..) (inf_le_right ..))

theorem sup_assoc (a b c : α) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) := by
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left ..) (le_trans (le_sup_left ..) (le_sup_right ..)))
      (le_trans (le_sup_right ..) (le_sup_right ..))
  · exact sup_le (le_trans (le_sup_left ..) (le_sup_left ..))
      (sup_le (le_trans (le_sup_right ..) (le_sup_left ..)) (le_sup_right ..))

@[simp] theorem inf_self (a : α) : a ⊓ a = a :=
  le_antisymm (inf_le_left ..) (le_inf (le_refl _) (le_refl _))

@[simp] theorem sup_self (a : α) : a ⊔ a = a :=
  le_antisymm (sup_le (le_refl _) (le_refl _)) (le_sup_left ..)

@[simp] theorem inf_top [OrderTop α] (a : α) : a ⊓ top = a :=
  le_antisymm (inf_le_left ..) (le_inf (le_refl _) (le_top _))

@[simp] theorem top_inf [OrderTop α] (a : α) : top ⊓ a = a := by
  rw [inf_comm, inf_top]

@[simp] theorem sup_bot [OrderBot α] (a : α) : a ⊔ bot = a :=
  le_antisymm (sup_le (le_refl _) (bot_le _)) (le_sup_left ..)

@[simp] theorem bot_sup [OrderBot α] (a : α) : bot ⊔ a = a := by
  rw [sup_comm, sup_bot]

@[simp] theorem inf_bot [OrderBot α] (a : α) : a ⊓ bot = bot :=
  le_antisymm (inf_le_right ..) (bot_le _)

@[simp] theorem bot_inf [OrderBot α] (a : α) : bot ⊓ a = bot := by
  rw [inf_comm, inf_bot]

@[simp] theorem sup_top [OrderTop α] (a : α) : a ⊔ top = top :=
  le_antisymm (le_top _) (le_sup_right ..)

@[simp] theorem top_sup [OrderTop α] (a : α) : top ⊔ a = top := by
  rw [sup_comm, sup_top]

end
scoped infix:50 (priority := high + 1) unicode(" ≤ ", " <= ") => NotationLE.le
scoped infix:50 (priority := high + 1) unicode(" ≥ ", " >= ") => fun a b => NotationLE.le b a

end Loom.Order
