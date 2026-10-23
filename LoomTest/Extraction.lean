import Loom

open MultiExtractor

namespace LoomTest.Extraction

-- Intentionally include a duplicate and use a noncanonical order. Correctness
-- alone does not detect reordered results or deduplicated execution traces.
private instance : Candidates (fun (_ : Bool) => True) where
  find := fun _ => [true, false, true]
  find_iff := by intro x; cases x <;> simp

private instance : ExtCandidates Candidates Bool (fun (_ : Bool) => True) where
  core := inferInstance
  rep := id

abbrev Target (α : Type) := TsilT (PeDivM (List Bool)) α

def pickBool : NonDetT DivM Bool := MonadNonDet.pickSuchThat Bool (fun _ => True)

def pickBoolExtracted : ConstrainedExtractResult Bool DivM Target
    (findOfCandidates Bool) pickBool := by
  unfold pickBool
  extract_list_tactic

def observe (xs : Target α) : List (List Bool × Option α) :=
  xs.map fun (log, result) => (log, match result with | .res a => some a | .div => none)

#guard observe pickBoolExtracted.val ==
  [([true], some true), ([false], some false), ([true], some true)]

def blocked : NonDetT DivM PUnit.{1} := MonadNonDet.assume False

def blockedExtracted : ConstrainedExtractResult Bool DivM Target
    (findOfCandidates Bool) blocked := by
  unfold blocked
  extract_list_tactic

#guard (observe blockedExtracted.val).isEmpty

def branching (b : Bool) : NonDetT DivM Bool := do
  let next := fun (x : Bool) => do
    let y ← pickBool
    pure (x && y)
  if b then next true else next false

def branchingExtracted (b : Bool) : ConstrainedExtractResult Bool DivM Target
    (findOfCandidates Bool) (branching b) := by
  unfold branching pickBool
  extract_list_tactic

#guard observe (branchingExtracted true).val == observe pickBoolExtracted.val
#guard observe (branchingExtracted false).val ==
  [([true], some false), ([false], some false), ([true], some false)]

def branchingInlineValues (b : Bool) : ConstrainedExtractResult Bool DivM Target
    (findOfCandidates Bool) (branching b) := by
  unfold branching pickBool
  extract_list_tactic -shareValueLets

#guard observe (branchingInlineValues true).val == observe (branchingExtracted true).val
#guard observe (branchingInlineValues false).val == observe (branchingExtracted false).val

-- Equal results alone do not detect duplicated continuations. Inspect the
-- elaborated value as well: extraction must retain a function-valued let.
open Lean Elab Command in
run_cmd do
  for name in [``branchingExtracted, ``branchingInlineValues] do
    let some info := (← getEnv).find? name | throwError "missing extraction result"
    let some value := info.value? | throwError "extraction result has no value"
    unless (value.find? fun
        | .letE _ ty _ _ _ => ty.isForall
        | _ => false).isSome do
      throwError "extraction no longer shares its join point: {name}"

def diverging : NonDetT DivM Bool := do
  let _ ← pickBool
  liftM (m := DivM) (DivM.div : DivM Bool)

def divergingExtracted : ConstrainedExtractResult Bool DivM Target
    (findOfCandidates Bool) diverging := by
  unfold diverging pickBool
  extract_list_tactic

#guard observe divergingExtracted.val ==
  [([true], none), ([false], none), ([true], none)]

-- A pick followed by its continuation, extracted with the continuation inside each
-- candidate's computation: the same results, logs and order as binding the pick's results.
def negated : NonDetT DivM Bool := do
  let y ← pickBool
  pure (!y)

def negatedExtracted : ConstrainedExtractResult Bool DivM Target
    (findOfCandidates Bool) negated := by
  unfold negated pickBool
  extract_list_tactic

def negatedPickBind : ConstrainedExtractResult Bool DivM Target
    (findOfCandidates Bool) negated := by
  unfold negated pickBool
  apply ConstrainedExtractResult.pickList_bind
  extract_list_tactic

def negatedAny : NonDetT DivM Bool := do
  let y ← MonadNonDet.pick Bool
  pure (!y)

def negatedAnyPickBind : ConstrainedExtractResult Bool DivM Target
    (findOfCandidates Bool) negatedAny := by
  unfold negatedAny
  apply ConstrainedExtractResult.pick_bind
  extract_list_tactic

#guard observe negatedExtracted.val ==
  [([true], some false), ([false], some true), ([true], some false)]
#guard observe negatedPickBind.val == observe negatedExtracted.val
#guard observe negatedAnyPickBind.val == observe negatedExtracted.val

-- Veil's executable stack, including its proof that logging preserves WP.
-- This checks the downstream simplification pattern affected by LogMonoid.
abbrev VeilTarget (κ ε ρ σ : Type) :=
  ReaderT ρ (ExceptT ε (StateT σ (TsilT (PeDivM (List κ)))))

open Loom.Order AngelicChoice TotalCorrectness in
example {κ ε ρ σ : Type} {hd : ε → Prop} [IsHandler hd] :
    LawfulMonadPersistentLog κ (VeilTarget κ ε ρ σ) (ρ → σ → Prop) where
  log_sound := by
    intro k post
    funext r st
    simp +instances +unfoldPartialApp [VeilTarget, Id, wp, liftM, monadLift,
      MAlg.lift, Functor.map, MAlgOrdered.μ, OfHd, MAlgExcept, pointwiseSup,
      ExceptT.map, ExceptT.mk, Except.getD, TsilTCore.op,
      StateT.map, StateT.pure, StateT.bind,
      MonadPersistentLog.log, MonadLift.monadLift, StateT.lift, ExceptT.lift,
      PeDivM.prependAll_eq, PeDivM.log, PeDivM.prepend, pure, bind, Loom.Order.embed]

/-! ## Names of picks in the log

A pick may carry the name of the variable that it is bound to, as Veil's frontend would give it.
Each candidate is then logged together with the name, which `Std.Format` entries show as `x = v`.
Picks without a name are logged as before, as the tests above check for `Bool` entries. -/

/-- The candidates satisfying a decidable predicate, out of all values listed in `all`. -/
@[reducible] private def candidatesOf (all : List α) (complete : ∀ a, a ∈ all) (p : α → Prop)
    [DecidablePred p] : Candidates p where
  find := fun _ => all.filter (decide <| p ·)
  find_iff := by intro x; simp [complete]

-- `low`, so that `pick Bool` keeps the candidates above, with their duplicate
private instance (priority := low) {p : Bool → Prop} [DecidablePred p] : Candidates p :=
  candidatesOf [true, false] (by decide) p

abbrev FormatTarget (α : Type) := TsilT (PeDivM (List Std.Format)) α

def logs (xs : FormatTarget α) : List (List String) :=
  xs.map fun (log, _) => log.map toString

-- Extracted pick by pick: `pick` would also match `pickSuchThat … (fun _ => True)` by unfolding,
-- and the other way round, losing the name; the fallback has to tell them apart.
def namedPicks : NonDetT DivM Bool := do
  let a ← MonadNonDet.pick Bool (name := "a")
  let b ← MonadNonDet.pickSuchThat Bool (fun c => c = !a) (name := "b")
  pure (a && b)

def namedPicksExtracted : ConstrainedExtractResult Std.Format DivM FormatTarget
    (findOfCandidates Std.Format) namedPicks := by
  unfold namedPicks
  extract_list_tactic

#guard logs namedPicksExtracted.val ==
  [["a = true", "b = false"], ["a = false", "b = true"], ["a = true", "b = false"]]

-- The same log, with the first pick extracted together with its continuation, as Veil does.
def namedPicksPickBind : ConstrainedExtractResult Std.Format DivM FormatTarget
    (findOfCandidates Std.Format) namedPicks := by
  unfold namedPicks
  apply ConstrainedExtractResult.pick_bind
  extract_list_tactic

#guard logs namedPicksPickBind.val == logs namedPicksExtracted.val

def unnamedPick : NonDetT DivM Bool := do
  let x ← MonadNonDet.pick Bool
  pure x

def unnamedPickExtracted : ConstrainedExtractResult Std.Format DivM FormatTarget
    (findOfCandidates Std.Format) unnamedPick := by
  unfold unnamedPick
  extract_list_tactic

#guard logs unnamedPickExtracted.val == [["true"], ["false"], ["true"]]

end LoomTest.Extraction
