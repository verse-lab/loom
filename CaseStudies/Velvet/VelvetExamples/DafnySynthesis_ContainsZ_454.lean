
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

method ContainsZ (s : Array Char) return (result : Bool)
  ensures result ↔ (∃ i, 0 ≤ i ∧ i < s.size ∧ (s[i]! = 'z' ∨ s[i]! = 'Z'))
do
  let mut result := false
  let mut i := 0
  while i < s.size ∧ result = false
    invariant 0 ≤ i ∧ i ≤ s.size
    invariant (result ↔ (∃ k, 0 ≤ k ∧ k < i ∧ (s[k]! = 'z' ∨ s[k]! = 'Z')))
    done_with (i = s.size ∨ result = true)
  do
    if s[i]! = 'z' ∨ s[i]! = 'Z' then
      result := true
    i := i + 1
  return result

prove_correct ContainsZ by
  loom_solve
  
