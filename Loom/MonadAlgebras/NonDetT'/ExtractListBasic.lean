import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.FinEnum

import Loom.MonadAlgebras.NonDetT'.Basic

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

instance {α : Type u} {p : α → Prop} [FinEnum α] [DecidablePred p] : Candidates p where
  find := fun _ => FinEnum.toList α |>.filter p
  find_iff := by simp

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

end MultiExtractor
