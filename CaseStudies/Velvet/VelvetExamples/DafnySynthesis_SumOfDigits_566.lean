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

attribute [local solverHint] Nat.mod_add_div

prove_correct SumOfDigits by
  unfold SumOfDigits SumDigits
  loom_solve
