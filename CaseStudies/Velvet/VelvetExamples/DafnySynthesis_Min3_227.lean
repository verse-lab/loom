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


method MinOfThree(a: Int) ( b: Int ) (c: Int) return (min: Int)
    ensures min <= a ∧  min <= b ∧  min <= c
    ensures (min = a) ∨  (min = b) ∨  (min = c)
    do
    let mut res := a
    if (a <= b ∧  a <= c) then
        res := a
    else 
      if (b <= a ∧  b <= c) then 
          res := b
      else 
          res := c
    return res


prove_correct MinOfThree by
  loom_solve
