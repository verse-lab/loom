import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 2
set_option auto.smt.solver.name "cvc5"

def SumDigits (n: Nat): Nat :=
  if n = 0 then 0
  else (n % 10) + SumDigits (n / 10)
termination_by n
decreasing_by grind

method SumOfDigits (number: Nat) return (sum: Nat)
    ensures sum = SumDigits number
do
    let mut sum := 0
    let mut n := number
    while n > 0
        invariant sum + SumDigits n = SumDigits number
        invariant 0 ≤ sum
        done_with n = 0
    do
        let digit := n % 10
        sum := sum + digit
        n := n / 10
    return sum

-- Key lemma: SumDigits unfolds according to its definition when n > 0
lemma SumDigits_unfold (n : Nat) (h : n > 0) :
  SumDigits n = (n % 10) + SumDigits (n / 10) := by
  rw [SumDigits]
  have h' : n ≠ 0 := Nat.ne_of_gt h
  simp [h']

-- Additional lemma: SumDigits is 0 when n = 0
lemma SumDigits_zero : SumDigits 0 = 0 := by
  unfold SumDigits
  simp

attribute [local solverHint] Nat.mod_add_div SumDigits_unfold SumDigits_zero

prove_correct SumOfDigits by
  loom_solve 
