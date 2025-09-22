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

method ContainsConsecutiveNumbers (a: Array Int) return (result: Bool)
    require a.size > 0
    ensures result ↔ (∃ i, 0 ≤ i ∧ i < a.size - 1 ∧ a[i]! + 1 = a[i+1]!)
do
    let mut result := false
    let mut i := 0
    while i < a.size - 1 ∧ result = false
        invariant 0 ≤ i ∧ i ≤ a.size - 1
        invariant result ↔ (∃ k, 0 ≤ k ∧ k < i ∧ a[k]! + 1 = a[k+1]!)
        done_with (i = a.size - 1 ∨ result = true)
    do
        if a[i]! + 1 = a[i+1]! then
            result := true
        i := i + 1
    return result

prove_correct ContainsConsecutiveNumbers by
  loom_solve
