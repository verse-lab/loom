import Init.Data.List.Lemmas

namespace Loom

/-- The operations and laws needed to accumulate logs. The combination may be
noncommutative; the order of events is observable. -/
class LogMonoid (ω : Type u) where
  empty : ω
  append : ω → ω → ω
  append_assoc : ∀ a b c, append (append a b) c = append a (append b c)
  empty_append : ∀ a, append empty a = a
  append_empty : ∀ a, append a empty = a

attribute [simp] LogMonoid.empty_append LogMonoid.append_empty

instance : LogMonoid (List α) where
  empty := []
  append := List.append
  append_assoc := List.append_assoc
  empty_append := List.nil_append
  append_empty := List.append_nil

instance : LogMonoid Unit where
  empty := ()
  append := fun _ _ => ()
  append_assoc := by intros; rfl
  empty_append := by rintro ⟨⟩; rfl
  append_empty := by rintro ⟨⟩; rfl

end Loom
