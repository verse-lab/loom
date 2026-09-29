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

end LoomTest.Extraction
