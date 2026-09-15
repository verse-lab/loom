module

public import Init.Data.Order.Lemmas

@[expose] public section

-- General-lattice facts over Lean's `LE`/`Min`/`Max` (Lean states most only for linear orders).

namespace Loom.Order

universe u v

export Std (le_refl le_trans le_antisymm le_of_eq)

scoped infixl:70 (priority := high) " ⊓ " => Min.min
scoped infixl:65 (priority := high) " ⊔ " => Max.max

attribute [scoped simp] Std.le_min_iff Std.max_le_iff
attribute [scoped simp] Std.min_le_left Std.min_le_right Std.left_le_max Std.right_le_max

theorem le_trans' {α : Type u} [LE α] [Std.IsPreorder α] {a b c : α}
    (h : b ≤ c) (k : a ≤ b) : a ≤ c :=
  le_trans k h

def Monotone {α : Type u} {β : Type v} [LE α] [LE β] (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

section Inf
variable {α : Type u} [LE α] [Min α] [Std.IsPartialOrder α] [Std.LawfulOrderInf α]
  {a b c d : α}

omit [Std.IsPartialOrder α] in
theorem le_inf (h : a ≤ b) (k : a ≤ c) : a ≤ b ⊓ c := Std.le_min_iff.mpr ⟨h, k⟩

theorem inf_le_of_left_le (h : a ≤ c) : a ⊓ b ≤ c := le_trans Std.min_le_left h
theorem inf_le_of_right_le (h : b ≤ c) : a ⊓ b ≤ c := le_trans Std.min_le_right h

theorem inf_mono (h : a ≤ b) (k : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
  le_inf (inf_le_of_left_le h) (inf_le_of_right_le k)

theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a :=
  le_antisymm (le_inf Std.min_le_right Std.min_le_left)
    (le_inf Std.min_le_right Std.min_le_left)

theorem inf_assoc (a b c : α) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) :=
  le_antisymm
    (le_inf (inf_le_of_left_le Std.min_le_left)
      (le_inf (inf_le_of_left_le Std.min_le_right) Std.min_le_right))
    (le_inf (le_inf Std.min_le_left (inf_le_of_right_le Std.min_le_left))
      (inf_le_of_right_le Std.min_le_right))

@[scoped simp] theorem inf_self (a : α) : a ⊓ a = a :=
  le_antisymm Std.min_le_left (le_inf (le_refl a) (le_refl a))

end Inf

section Sup
variable {α : Type u} [LE α] [Max α] [Std.IsPartialOrder α] [Std.LawfulOrderSup α]
  {a b c d : α}

omit [Std.IsPartialOrder α] in
theorem sup_le (h : a ≤ c) (k : b ≤ c) : a ⊔ b ≤ c := Std.max_le_iff.mpr ⟨h, k⟩

theorem le_sup_of_le_left (h : a ≤ b) : a ≤ b ⊔ c := le_trans h Std.left_le_max
theorem le_sup_of_le_right (h : a ≤ c) : a ≤ b ⊔ c := le_trans h Std.right_le_max

theorem sup_mono (h : a ≤ b) (k : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
  sup_le (le_sup_of_le_left h) (le_sup_of_le_right k)

theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a :=
  le_antisymm (sup_le Std.right_le_max Std.left_le_max)
    (sup_le Std.right_le_max Std.left_le_max)

@[scoped simp] theorem sup_self (a : α) : a ⊔ a = a :=
  le_antisymm (sup_le (le_refl a) (le_refl a)) Std.left_le_max

end Sup

section
variable {α : Type u} [LE α] [Min α] [Max α] [Std.IsPartialOrder α]
  [Std.LawfulOrderInf α] [Std.LawfulOrderSup α]

@[scoped simp] theorem inf_le_sup_ll (a b c : α) : a ⊓ b ≤ a ⊔ c := le_sup_of_le_left Std.min_le_left
@[scoped simp] theorem inf_le_sup_lr (a b c : α) : a ⊓ b ≤ c ⊔ a := le_sup_of_le_right Std.min_le_left
@[scoped simp] theorem inf_le_sup_rl (a b c : α) : a ⊓ b ≤ b ⊔ c := le_sup_of_le_left Std.min_le_right
@[scoped simp] theorem inf_le_sup_rr (a b c : α) : a ⊓ b ≤ c ⊔ b := le_sup_of_le_right Std.min_le_right

end

end Loom.Order
