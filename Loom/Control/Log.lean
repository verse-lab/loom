module

public import Init.Data.List.Lemmas

@[expose] public section

namespace Loom

/-- The operations and laws needed to accumulate logs. The combination may be
noncommutative; the order of events is observable. -/
class LogMonoid (ω : Type u) where
  empty : ω
  append : ω → ω → ω
  [toAssociative : Std.Associative append]
  [toLawfulIdentity : Std.LawfulIdentity append empty]

attribute [instance] LogMonoid.toAssociative LogMonoid.toLawfulIdentity

namespace LogMonoid
variable [LogMonoid ω]

theorem append_assoc (a b c : ω) : append (append a b) c = append a (append b c) :=
  Std.Associative.assoc a b c

@[simp] theorem empty_append (a : ω) : append empty a = a :=
  Std.LawfulLeftIdentity.left_id a

@[simp] theorem append_empty (a : ω) : append a empty = a :=
  Std.LawfulRightIdentity.right_id a
end LogMonoid

@[inline]
instance : LogMonoid (List α) where
  empty := []
  append := List.append
  toAssociative := inferInstanceAs (Std.Associative (fun a b : List α => a ++ b))
  toLawfulIdentity := inferInstanceAs (Std.LawfulIdentity (fun a b : List α => a ++ b) [])

instance : LogMonoid Unit where
  empty := ()
  append := fun _ _ => ()
  toAssociative := ⟨by intros; rfl⟩
  toLawfulIdentity := { left_id := by rintro ⟨⟩; rfl, right_id := by rintro ⟨⟩; rfl }

end Loom
