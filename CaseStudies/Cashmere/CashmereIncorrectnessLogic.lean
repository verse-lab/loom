import Loom.MonadAlgebras.Instances.StateT
import Loom.MonadAlgebras.Instances.ExceptT
import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'
import Lean

import CaseStudies.Cashmere.Syntax_Cashmere

open Lean.Elab.Term.DoNames

open Queue

open ExceptionAsSuccess

instance : MonadExceptOf String CashmereM where
  throw e := liftM (m := ExceptT String (StateT Balance DivM)) (throw e)
  tryCatch := fun x _ => x

open TotalCorrectness AngelicChoice


#derive_lifted_wp for (get : StateT Balance DivM Balance) as CashmereM Balance
#derive_lifted_wp (res: Balance) for (set res : StateT Balance DivM PUnit) as CashmereM PUnit
#derive_lifted_wp (s : String) for (throw s : ExceptT String (StateT Balance DivM) PUnit) as CashmereM PUnit
--small aesop upgrade
add_aesop_rules safe (by linarith)

bdef withdrawSessionAngelic returns (u: Unit)
  require balance > 0
  ensures False do
  let mut amounts ← pick (Queue Nat)
  while amounts.nonEmpty
  invariant balance >= 0
  invariant balance < amounts.sum
  decreasing amounts.length
  do
    let amount := amounts.dequeue
    if amount > balance then
      throw "Insufficient funds"
    else
      balance := balance - amount
    amounts := amounts.tail
  return


@[aesop safe]
theorem Queue.sum_lt (x: Balance) : x < y -> x < (Queue.mk [Int.toNat y]).sum := by intro h; simp [Queue.sum, *]
@[aesop safe]
theorem balance_lt (x: Balance) : x < x + 1 := by linarith


prove_correct withdrawSessionAngelic by
  dsimp [withdrawSessionAngelic]
  loom_solve!
