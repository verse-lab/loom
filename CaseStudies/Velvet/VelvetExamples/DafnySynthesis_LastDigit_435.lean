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

--method LastDigit(n: int) returns (d: int)
    --requires n >= 0
    --ensures 0 <= d < 10
    --ensures n % 10 == d
--{
    --d := n % 10;
--}

method LastDigit
  (n: Nat) return (d: Nat)
    ensures d < 10
    ensures n % 10 = d
    do
    return n % 10

attribute [local solverHint] Nat.mod_lt

-- loom_solve couldn't finish the proof probably because of mod, added the hint and proof goes through
prove_correct LastDigit by
  loom_solve
