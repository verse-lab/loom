module

public import Loom.MonadAlgebras.NonDetT'.Basic

@[expose] public section

open Loom Loom.Order

namespace MultiExtractor

class Candidates {α : Type u} (p : α → Prop) where
  find : Unit → List α
  find_iff : ∀ x, x ∈ find () ↔ p x

class PartialCandidates {α : Type u} (p : α → Prop) where
  find : Unit → List α
  find_then : ∀ x, x ∈ find () → p x

-- class Representable (κ : Type u) (c : {τ : Type u} → (τ → Prop) → Type u) where
--   rep : ∀ {τ} {p : τ → Prop}, c p → τ → κ

-- class ChoiceRepresentable (τ κ : Type u) where
--   rep : τ → κ

class ExtCandidates (c : {τ : Type u} → (τ → Prop) → Type u) (κ : Type w) {α : Type u} (p : α → Prop) where
  core : c p
  rep : α → κ

-- def ExtCandidates (c : {τ : Type u} → (τ → Prop) → Type u) (κ : Type w) : {τ : Type u} → (τ → Prop) → Type _ :=
--   fun {τ} p => (c p × (τ → κ))

-- def ExtCandidates.proj1 {κ : Type u} {c : {τ : Type u} → (τ → Prop) → Type u} {τ : Type u} {p : τ → Prop} :
--   ExtCandidates c κ p → c p := Prod.fst

-- def ExtCandidates.proj2 {κ : Type u} {c : {τ : Type u} → (τ → Prop) → Type u} {τ : Type u} {p : τ → Prop} :
--   ExtCandidates c κ p → τ → κ := Prod.snd

instance PartialCandidates.of_Candidates {α : Type u} (p : α → Prop) [Candidates p] : PartialCandidates p where
  find := Candidates.find p
  find_then := by intro x hx ; rw [Candidates.find_iff] at hx ; exact hx


-- FIXME: `PartialCandidates` can be sampled. maybe add one such construction?

-- TODO is this allowed? or we need repetition? maybe just changing `[c p]` into `(c p)` would work
set_option checkBinderAnnotations false in
instance [inst : c p] : ExtCandidates c Unit p where
  core := inst
  rep := fun _ => ()

-- instance [inst : PartialCandidates p] : ExtCandidates PartialCandidates Unit p where
--   core := inst
--   rep := fun _ => ()

set_option checkBinderAnnotations false in
instance (priority := low) [inst : c p] : ExtCandidates c Std.Format p where
  core := inst
  rep := fun _ => "not representable"

set_option checkBinderAnnotations false in
instance {p : α → Prop} [inst : c p] [instr : Repr α] : ExtCandidates c Std.Format p where
  core := inst
  rep := fun a => instr.reprPrec a 0

set_option checkBinderAnnotations false in
instance [inst : c p] : ExtCandidates c (Sigma id) p where
  core := inst
  rep := fun a => ⟨_, a⟩

/-! ## Names of choices in the log

A choice may carry the name of the variable that it is bound to (the `name` of `MonadNonDet.pick`
and `MonadNonDet.pickSuchThat`). Extraction logs each candidate together with that name, in one
log entry, so that the log stays the sequence of choices of an execution. How a name and a
candidate make one entry depends on the type `κ` of the entries. -/

/-- How a log entry of type `κ` records the name of the variable that a choice is bound to. -/
class NamedRep (κ : Type w) where
  withName : String → κ → κ

/-- By default, the name is dropped, so the log is the same as without names. -/
instance (priority := low) : NamedRep κ where
  withName _ k := k

instance : NamedRep Std.Format where
  withName n f := .text n ++ " = " ++ f

/-- `ec`, with each candidate logged together with the name `n` of the variable it is bound to,
if there is one. The candidates are those of `ec.core`, as before. -/
abbrev ExtCandidates.named {c : {τ : Type u} → (τ → Prop) → Type u} {κ : Type w} {α : Type u}
    {p : α → Prop} [NamedRep κ] : Option String → ExtCandidates c κ p → ExtCandidates c κ p
  | none, ec => ec
  | some n, ec => { core := ec.core, rep := fun a => NamedRep.withName n (ec.rep a) }

end MultiExtractor
