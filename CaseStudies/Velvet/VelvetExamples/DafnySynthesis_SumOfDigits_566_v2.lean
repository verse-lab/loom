import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

-- Simple recursive definition for sum of digits
def SumDigits (n: Nat): Nat :=
  if n < 10 then n else (n % 10) + SumDigits (n / 10)
termination_by n
decreasing_by simp_wf; omega

method SumOfDigits (number: Nat) return (sum: Nat)
    require number ≥ 0
    ensures sum ≥ 0
    ensures sum = SumDigits number
do
    let mut sum := 0
    let mut n := number

    while n > 0
        invariant sum + SumDigits n = SumDigits number
        invariant sum ≥ 0
        done_with n = 0
    do
        let digit := n % 10
        sum := sum + digit
        n := n / 10
    return sum

-- Helper lemmas
lemma sumDigits_zero : SumDigits 0 = 0 := by simp [SumDigits]

lemma sumDigits_single_digit (n : Nat) (h : n < 10) :
    SumDigits n = n := by simp [SumDigits, h]

lemma sumDigits_step (n : Nat) (h : n ≥ 10) :
    SumDigits n = (n % 10) + SumDigits (n / 10) := by
  rw [SumDigits]
  split
  · omega  -- contradiction since n ≥ 10 but n < 10
  · rfl    -- definition matches exactly

attribute [local solverHint] Nat.mod_add_div sumDigits_step sumDigits_zero sumDigits_single_digit

prove_correct SumOfDigits by
  unfold SumOfDigits
  loom_solve
