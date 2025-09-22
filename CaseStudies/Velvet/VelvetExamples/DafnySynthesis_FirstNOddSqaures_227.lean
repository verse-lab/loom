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

method SumOfSquaresOfFirstNOddNumbers (n: Nat) return (sum: Nat)
    ensures sum = (n * (2 * n - 1) * (2 * n + 1)) / 3
    do
    let mut sum := 0;
    let mut i := 1;
    let mut k := 0
    while k < n
    invariant 0 <= k ∧ k <= n
    invariant sum = k * (2 * k - 1) * (2 * k + 1) / 3
    invariant i = 2 * k + 1
    done_with k = n
    do
        sum := sum + i * i;
        i := i + 2;
        k := k + 1
    return sum


prove_correct SumOfSquaresOfFirstNOddNumbers by
  loom_solve
