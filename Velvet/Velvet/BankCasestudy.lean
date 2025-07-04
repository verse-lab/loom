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

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 10
set_option auto.smt.solver.name "cvc5"

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

#check MonadExcept

section

open ExceptionAsFailure PartialCorrectness DemonicChoice



@[spec, loomWpSimp]
noncomputable
def BankM.wp_get: WPGen (get : BankM Balance) where
    get := fun fn x => fn x x
    prop := fun post => by
      simp [instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,getThe]
      simp [NonDetT.wp_lift, MPropLift.wp_lift]
      erw [StateT.wp_get]


@[spec, loomWpSimp]
def BankM.wp_set (res: Balance) : WPGen (set res : BankM PUnit) where
    get := fun fn x => fn PUnit.unit res
    prop := fun post => by
      simp [instMonadStateOfMonadStateOf, instMonadStateOfOfMonadLift,getThe]
      simp [NonDetT.wp_lift, MPropLift.wp_lift]
      simp [StateT.wp_eq, set, StateT.set, wp_pure]

end

open ExceptionAsFailure
/-
instance: MPropOrdered (ExceptT String (StateT Balance DivM)) (Balance -> Prop) where
  μ := fun f pred =>
    match (f pred) with
    | .div => False
    | .res (.ok res, x) => res x
    | .res (.error err, x) => False
  μ_ord_pure := fun l => by simp [pure, ExceptT.pure, ExceptT.mk, StateT.pure]
  μ_ord_bind := fun {α} f g => by
    intro leq x
    simp [LE.le] at leq
    simp [LE.le, bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont]
    intro b
    simp [ExceptT, StateT] at x
    match (x b) with
    | .div => simp
    | .res (.error err, y) => simp
    | .res (.ok res, y) => simp; exact leq res y
-/
/-
returns (x : T)
require P
ensures Q do
code

∀ balanceOld,
  triple
    (fun balance => balance = balanceOld ∧ P)
    code
    (fun x balance => Q)

-/

bdef withdraw (amount : Nat) returns (u: Unit)
  ensures balance + amount = balanceOld do
  balance := balance - amount
  return
open PartialCorrectness DemonicChoice in
prove_correct withdraw by
  dsimp [withdraw]; intro
  mwp; simp [loomLogicSimp, loomWpSimp]

/-
After all the macro-expansion, the code above expands exactly to the code in \todo{},
which one can simply run in \lean unsing \code{StateM.run} function.
Also it will generate a corresponding correctness theorem for \code{withdraw} function
based on the \code{ensures} annotation.
We will discuss how this statement looks like and what is required to define it in the next section.

-/

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
  simp [triple, withdrawSession]
  loom_intro
  mwp; simp [loomLogicSimp, loomWpSimp]


  constructor
  { intro b x
    constructor
    { intro pos
      rw [Queue.tail]
      simp [Queue.nonEmpty] at pos
      split
      { contradiction }
      simp [Queue.dequeue]
      rename_i x1 x2 x3 x4
      simp [x4]
      rw [add_sub, ←x]
      simp [Queue.sum, x4]
      ring }
    intro neg
    constructor
    { exact x }
    exact neg }

  rintro ⟨amt, bal⟩
  intro x nemp
  simp
  simp [Queue.nonEmpty] at nemp
  nth_rw 1 [Queue.sum] at x
  simp [nemp] at x
  simp [x]
  rw [add_comm]



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
  simp [triple, withdrawSessionTot]
  loom_intro
  mwp
  { apply WPGen.setm }
  simp [loomLogicSimp, loomWpSimp]
  constructor
  { loom_intro
    intro h
    constructor
    { intro pos
      rw [Queue.tail]
      simp [Queue.nonEmpty] at pos
      split
      { contradiction }
      simp [Queue.dequeue]
      rename_i x1 x2 x3 x4
      simp [x4]
      rw [add_sub, ←h]
      simp [Queue.sum, x4]
      ring_nf
      simp [Queue.length, x4] }
    intro neg
    simp [neg, h] }
  loom_intro
  intro x nemp
  simp [Queue.nonEmpty] at nemp
  nth_rw 1 [Queue.sum] at x
  simp [nemp] at x
  simp [x]
  rw [add_comm]

instance: MonadExcept String (NonDetT (StateT Balance DivM)) where
  throw := sorry
  tryCatch := sorry

open TotalCorrectness DemonicChoice in
bdef withdrawSessionExcept (inAmounts : Queue Nat) returns (u: Unit)
  require balance >= inAmounts.sum
  ensures balance >= 0
  ensures balance + inAmounts.sum = balanceOld do
  let mut amounts := inAmounts
  let balanceOld := balance
  while (amounts.nonEmpty)
  invariant inAmounts.sum + balanceOld = amounts.sum + balance
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
  simp [triple, withdrawSessionExcept]
  loom_intro
  mwp
  { sorry }
  { sorry }
  sorry

/-
def qlem: Queue Nat := { elems := []}

bdef withdrawSessionNonDet returns (history : Queue Nat)
  require balance >= 0
  ensures balance >= 0
  ensures balanceNew + history.sum = balance do
  let inAmounts: Queue Nat := ∗ change this to NonDet
  let mut amounts := inAmounts
  let balanceOld := balance
  while amounts.nonEmpty
  invariant inAmounts.sum + balanceOld = amounts.sum + balance
  invariant balance >= amounts.sum
  decreasing amounts.length do
    let amount := amounts.dequeue
    if amount > balance then
      throw "Insufficient funds"
    else
      balance := balance - amount
    amounts := amounts.tail
  return inAmounts

prove_correct withdrawSessionNonDet by
  simp [triple, withdrawSessionNonDet]
  loom_intro
  mwp
  { sorry }
  { sorry }
  { sorry }
  sorry
-/
/-We are going to demonstrate \tool by building a multi-modal
  verifier for a simple imperative \while-style langauge (with
  additional goodies). We can follow the simple structure, each item
  below is a subsection.-/
/-
Shallow embedding the \while language, its runtime semantics
Better syntax via \lean metaprorgamming
Implementing a VC generator, establishing its soundness
Adding effects: divergence and exceptions, what happens to the VC generator
Introducing non-determinism, handlining it demonically
Angelic handling of non-determinis a la incorrectness logic
Putting it all together: verifying a small non-trivial program
Putting it all together: verify a simple program or its version,
  in a combined interactive/automated mode. Some examples for
  tinkering are here.\footnote{https://chatgpt.com/share/68623a8d-9d34-8006-8dfb-7be04fefe08f}
-/
