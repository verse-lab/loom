import Init.Data.List.Lemmas

namespace Loom.List

/-- Flat-mapping two functions that agree on the input list gives equal results. -/
theorem flatMap_congr {xs : List α} {f g : α → List β}
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]

end Loom.List
