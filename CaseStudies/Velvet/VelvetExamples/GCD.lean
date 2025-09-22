import Auto
import Lean

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open TotalCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

-- The Euclidean algorithm for GCD is a classic example of a function requiring
-- explicit termination measures due to the modulo operation

method gcd (a : Nat) (b : Nat) return (res : Nat)
  require b > 0
  ensures res > 0
  do
    if a % b = 0 then
      return b
    else
      let remainder := a % b
      let result ← gcd b remainder
      return result.1
  termination_by b
  decreasing_by
    apply Nat.mod_lt
    sorry -- Termination proof would need access to precondition b > 0, TODO: need support from velvet

-- Add modulo hints for the SMT solver
attribute [solverHint] Nat.mod_lt

prove_correct gcd by
  loom_solve
termination_by b
decreasing_by all_goals(
  -- Looking at the goals, we can see the precondition is in the context
  -- We need to extract b > 0 from the WithName wrapper
  have h : b > 0 := by
    -- The precondition should be available in the inductive hypothesis
    sorry -- TODO: need way to access precondition from context
  apply Nat.mod_lt
  assumption
  )
