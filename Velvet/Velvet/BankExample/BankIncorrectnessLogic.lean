import Loom.MonadAlgebras.Instances.StateT
import Loom.MonadAlgebras.Instances.ExceptT
import Loom.MonadAlgebras.NonDetT.Extract
import Velvet.BankExample.Syntax_bank
import Mathlib.Tactic
import Loom.MonadAlgebras.WP.DoNames'
import Lean

import Loom.MonadAlgebras.WP.Tactic

import Velvet.Extension
import Velvet.Tactic

open Lean.Elab.Term.DoNames

open Queue

open ExceptionAsSuccess

instance : MonadExceptOf String BankM where
  throw e := liftM (m := ExceptT String (StateT Balance DivM)) (throw e)
  tryCatch := fun x _ => x

open TotalCorrectness AngelicChoice

@[spec, loomWpSimp]
noncomputable
def BankM.wp_get_totl: WPGen (get : BankM Balance) := by
  econstructor; intro post
  have : get = liftM (n := BankM) (liftM (n := (ExceptT String (StateT Balance DivM))) (get : StateT Balance DivM Balance)) := by
    rfl
  rewrite [this]
  simp [NonDetT.wp_lift, MAlgLift.wp_lift]
  rw [StateT.wp_get]


@[spec, loomWpSimp]
def BankM.wp_set_totl (res: Balance) : WPGen (set res : BankM PUnit) := by
  econstructor; intro post
  have : set res = liftM (n := BankM) (liftM (n := (ExceptT String (StateT Balance DivM))) (set res : StateT Balance DivM PUnit)) := by
    rfl
  rewrite [this]
  simp [NonDetT.wp_lift, MAlgLift.wp_lift]
  rw [StateT.wp_set]

@[spec, loomWpSimp]
noncomputable
def BankM.wp_throw_totl (s: String) : WPGen (throw s: BankM PUnit) := by
  econstructor; intro post
  have : throw s = liftM (n := BankM) (throw s : ExceptT String (StateT Balance DivM) PUnit) := by
    rfl
  rewrite [this]
  simp [NonDetT.wp_lift, MAlgLift.wp_lift]
  rw [ExceptT.wp_throw]

--small aesop upgrade
add_aesop_rules safe (by linarith)

bdef withdrawSessionAngelic returns (u: Unit)
  require balance > 0
  ensures False do
  let mut amounts: Queue Nat ← pick (Queue Nat)
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

@[aesop norm]
theorem mkQueue (x: Balance) : ∃ q: Queue Nat, x < q.sum := by exists {elems := [Int.toNat (x + 1)]}; simp [Queue.sum]

prove_correct withdrawSessionAngelic by
  dsimp [withdrawSessionAngelic]
  loom_solve
