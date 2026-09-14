import Init.Data.List.Lemmas

namespace Loom.List

/-- Flat-mapping two functions that agree on the input list gives equal results. -/
theorem flatMap_congr {xs : List α} {f g : α → List β}
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g :=
  congrArg List.flatten (List.map_congr_left h)

end Loom.List
