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


method Minimum (a: Int) (b: Int) return (minValue: Int)
    ensures minValue = a ∨ minValue = b
    ensures minValue <= a ∧ minValue <= b
    do
    let mut minValue := a
    if a <= b then
        minValue := a
    else 
        minValue := b
    return minValue


prove_correct Minimum by
  loom_solve
