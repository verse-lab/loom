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
  /-- A cheap test for `empty`, so that consumers can skip appending an empty log.
  Answering `false` is always sound: it only disables such fast paths. Define it by
  an inline `match` so that the test folds away when the log is statically known. -/
  isEmpty : ω → Bool := fun _ => false
  eq_empty_of_isEmpty : ∀ w, isEmpty w = true → w = empty := by intro _ h; cases h

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
  -- Not `List.isEmpty`: it is not inlined, so the test on a literal `[]` would not fold away
  isEmpty := fun | [] => true | _ :: _ => false
  eq_empty_of_isEmpty := fun | [], _ => rfl

instance : LogMonoid Unit where
  empty := ()
  append := fun _ _ => ()
  toAssociative := ⟨by intros; rfl⟩
  toLawfulIdentity := { left_id := by rintro ⟨⟩; rfl, right_id := by rintro ⟨⟩; rfl }
  isEmpty := fun _ => true
  eq_empty_of_isEmpty := fun _ _ => rfl

end Loom
