import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Basic
import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std

open Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"


attribute [solverHint] TArray.get_set TArray.size_set

variable {arrInt} [arr_inst_int: TArray Int arrInt]
variable {arrNat} [arr_inst: TArray Nat arrNat]

-- set_option trace.profiler true
attribute [local solverHint] TArray.multiSet_swap

--we prove invariants in partial correctness
open PartialCorrectness DemonicChoice in
method insertionSort_part
  (mut arr: arrInt) return (u: Unit)
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < size arr → arrNew[i] ≤ arrNew[j]
  ensures toMultiset arr = toMultiset arrNew
  do
    let arr₀ := arr
    let arr_size := size arr
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ size arr
      invariant size arr = arr_size
      invariant n ≤ size arr
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i] ≤ arr[j]
      invariant toMultiset arr = toMultiset arr₀
      do
        let mut mind := n
        while mind ≠ 0
        invariant size arr = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i] ≤ arr[j]
        invariant toMultiset arr = toMultiset arr₀
        do
          if arr[mind] < arr[mind - 1] then
            swap arr[mind] arr[mind - 1]
          mind := mind - 1
        n := n + 1
      return
open PartialCorrectness DemonicChoice in
prove_correct insertionSort_part by
  loom_solve!

--we prove termination in total correctness
open TotalCorrectness DemonicChoice in
method insertionSort_termination
  (mut arr: arrInt) return (u: Unit)
  ensures True
  do
    let arr₀ := arr
    let arr_size := size arr
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ size arr
      invariant size arr = arr_size
      invariant n ≤ size arr
      decreasing size arr - n
      do
        let mut mind := n
        while mind ≠ 0
        invariant size arr = arr_size
        decreasing mind
        do
          if arr[mind] < arr[mind - 1] then
            swap arr[mind] arr[mind - 1]
          mind := mind - 1
        n := n + 1
      return
open TotalCorrectness DemonicChoice in
prove_correct insertionSort_termination by
  loom_solve!

--we prove the postcondition just by combination of the two triples above
open TotalCorrectness DemonicChoice in
method insertionSort_result
  (mut arr: arrInt) return (u: Unit)
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < size arr → arrNew[i] ≤ arrNew[j]
  ensures toMultiset arr = toMultiset arrNew
  do
    let arr₀ := arr
    let arr_size := size arr
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ size arr
      invariant True
      do
        let mut mind := n
        while mind ≠ 0
        invariant True
        do
          if arr[mind] < arr[mind - 1] then
            swap arr[mind] arr[mind - 1]
          mind := mind - 1
        n := n + 1
      return
open TotalCorrectness DemonicChoice in
prove_correct insertionSort_result by
  have triple_termination := insertionSort_termination_correct arr
  have triple_res := insertionSort_part_correct arr
  -- applying lemma about separation of termination proof and correctness proof
  exact VelvetM.total_decompose_triple
    (insertionSort_termination arr) (insertionSort_part arr) (insertionSort_result arr)
    (eqx := by rfl) (eqy := by rfl)
    triple_termination
    triple_res
