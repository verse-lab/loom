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


method KthElement(arr: Array Int) (k: Nat) return (result: Int)
  require 1 <= k ∧ k <= arr.size
  ensures result = arr[k - 1]!
  do
  return arr[k - 1]!

prove_correct KthElement by
  loom_solve
