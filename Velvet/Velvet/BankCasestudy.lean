import Loom.MonadAlgebras.Instances.StateT
import Loom.MonadAlgebras.Instances.ExceptT
import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.NonDetT.Basic
import Velvet.Syntax_bank
import Mathlib.Tactic
import Loom.MonadAlgebras.WP.DoNames'
import Auto
import Lean

import Loom.MonadAlgebras.WP.Tactic

import Velvet.Extension
import Velvet.Tactic

open Lean.Elab.Term.DoNames

open Queue
/-
In this section we are going to demonstrate \tool by building a multi-modal verifier for a simple
imperative \while-style language shallowly embedded into \lean.
We will illustrate how one can extend language with additional effects in \tool
on a simple example implementing a procedure for a safe back withdrawal.
-/
/-We start with a simple example of a function that withdraws
an amount from a balance implemented in a lean State monad.
-/
/-
The state of \code{withdraw} procedure is the integer balance value.
The function \code{withdraw} reads the current balance from the state (line 3),
and then updates the state with the new decremented balance (line 4).
%
Now, to make this code look more like imperative code,
we can implemented some macro-expansion to add a \code{balance := ...}
syntax to update the balance state as well as,
\code{return} statement to specify the return value and \code{require/ensures} statements
to specify the pre- and post-conditions.
%
-/


open ExceptionAsFailure

instance mlift : MonadLift (ExceptT String (StateT Balance DivM)) BankM where
  monadLift x := NonDetT.vis x pure

instance : MonadExceptOf String BankM where
  throw e := mlift.monadLift (throw e)
  tryCatch := sorry

section


open PartialCorrectness DemonicChoice

@[spec, loomWpSimp]
noncomputable
def BankM.wp_get_part: WPGen (get : BankM Balance) where
    get := fun fn x => fn x x
    prop := fun post => by
      simp [instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,getThe]
      simp [NonDetT.wp_lift, MPropLift.wp_lift]
      erw [StateT.wp_get]

@[spec, loomWpSimp]
def BankM.wp_set_part (res: Balance) : WPGen (set res : BankM PUnit) where
    get := fun fn x => fn PUnit.unit res
    prop := fun post => by
      simp [instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,getThe]
      simp [NonDetT.wp_lift, MPropLift.wp_lift]
      simp [StateT.wp_eq, set, StateT.set, wp_pure]

@[spec, loomWpSimp]
noncomputable
def BankM.wp_throw_part (s: String) : WPGen (throw s: BankM PUnit) where
    get := fun fn x => ⊥
    prop := fun post => by
      simp [throw, instMonadExceptOfMonadExceptOf, throwThe, MonadExceptOf]
      rw [MonadExceptOf.throw, instMonadExceptOfStringBankM]
      simp [mlift, ExceptT.wp_throw]
      rfl

end

section

open TotalCorrectness DemonicChoice

@[spec, loomWpSimp]
noncomputable
def BankM.wp_get_totl: WPGen (get : BankM Balance) where
    get := fun fn x => fn x x
    prop := fun post => by
      simp [instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,getThe]
      simp [NonDetT.wp_lift, MPropLift.wp_lift]
      erw [StateT.wp_get]


@[spec, loomWpSimp]
def BankM.wp_set_totl (res: Balance) : WPGen (set res : BankM PUnit) where
    get := fun fn x => fn PUnit.unit res
    prop := fun post => by
      simp [instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,getThe]
      simp [NonDetT.wp_lift, MPropLift.wp_lift]
      simp [StateT.wp_eq, set, StateT.set, wp_pure]

@[spec, loomWpSimp]
noncomputable
def BankM.wp_throw_totl (s: String) : WPGen (throw s: BankM PUnit) where
    get := fun fn x => ⊥
    prop := fun post => by
      simp [throw, instMonadExceptOfMonadExceptOf, throwThe, MonadExceptOf]
      rw [MonadExceptOf.throw, instMonadExceptOfStringBankM]
      simp [mlift, ExceptT.wp_throw]
      rfl
end

--small aesop upgrade
add_aesop_rules safe (by linarith)

bdef withdraw (amount : Nat) returns (u: Unit)
  ensures balance + amount = balanceOld do
  balance := balance - amount
  return

open PartialCorrectness DemonicChoice in
prove_correct withdraw by
  dsimp [withdraw]; intro
  velvet_intro; velvet_unfold
  aesop

open PartialCorrectness DemonicChoice in
bdef withdrawSession (inAmounts : Queue Nat) returns (u: Unit)
  ensures balance + inAmounts.sum = balanceOld do
  let mut amounts := inAmounts
  let balancePrev := balance
  while (amounts.nonEmpty)
  invariant amounts.sum + balancePrev = inAmounts.sum + balance
  do
    let amount := amounts.dequeue
    balance := balance - amount
    amounts := amounts.tail
  return


open PartialCorrectness DemonicChoice in
prove_correct withdrawSession by
  dsimp [withdrawSession]
  loom_intro
  velvet_intro <;> velvet_unfold <;> aesop

open TotalCorrectness DemonicChoice in
bdef withdrawSessionTot (inAmounts : Queue Nat) returns (u: Unit)
  ensures balance + inAmounts.sum = balanceOld do
  let mut amounts := inAmounts
  let balancePrev := balance
  while (amounts.nonEmpty)
  invariant amounts.sum + balancePrev = inAmounts.sum + balance
  decreasing amounts.length
  do
    let amount := amounts.dequeue
    balance := balance - amount
    amounts := amounts.tail
  return

open TotalCorrectness DemonicChoice in
prove_correct withdrawSessionTot by
  dsimp [withdrawSessionTot]
  loom_intro
  velvet_intro <;> velvet_unfold <;> aesop

open TotalCorrectness DemonicChoice in
bdef withdrawSessionExcept (inAmounts : Queue Nat) returns (u: Unit)
  require balance >= inAmounts.sum
  ensures balance >= 0
  ensures balance + inAmounts.sum = balanceOld do
  let mut amounts := inAmounts
  let balancePrev := balance
  while (amounts.nonEmpty)
  invariant amounts.sum + balancePrev = inAmounts.sum + balance
  invariant balance >= amounts.sum
  decreasing amounts.length do
    let amount := amounts.dequeue
    if amount > balance then
      throw "Insufficient funds"
    else
      balance := balance - amount
    amounts := amounts.tail
  return

open TotalCorrectness DemonicChoice in
prove_correct withdrawSessionExcept by
  dsimp [withdrawSessionExcept]
  loom_intro
  velvet_intro <;> velvet_unfold <;> aesop

open TotalCorrectness DemonicChoice in
bdef withdrawSessionNonDet returns (history : Queue Nat)
  require balance >= 0
  ensures balance >= 0
  ensures balance + history.sum = balanceOld do
  let inAmounts: Queue Nat ← pickSuchThat (Queue Nat) (fun q => q.sum ≤ balance)
  let mut amounts := inAmounts
  let balancePrev := balance
  while amounts.nonEmpty
  invariant amounts.sum + balancePrev = inAmounts.sum + balance
  invariant balance >= amounts.sum
  decreasing amounts.length do
    let amount := amounts.dequeue
    if amount > balance then
      throw "Insufficient funds"
    else
      balance := balance - amount
    amounts := amounts.tail
  return inAmounts

open TotalCorrectness DemonicChoice in
prove_correct withdrawSessionNonDet by
  dsimp [withdrawSessionNonDet]
  loom_intro
  velvet_intro
  velvet_unfold
  aesop

#eval (withdraw 2).run.run.run 10
#eval (withdrawSession ({elems := [1, 2, 6]})).run.run.run 12

#eval! (withdrawSessionExcept ({elems := {1,2,3}})).run.run.run 8
#eval! (withdrawSessionExcept ({elems := [1,2,6]})).run.run.run 8
