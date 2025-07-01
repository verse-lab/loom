import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import Velvet.Extension
import Velvet.Syntax
import Velvet.Tactic
import Velvet.Std

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

set_option quotPrecheck false in
notation "[totl|" t "]" => open TotalCorrectness TotalCorrectness.DemonicChoice in t
set_option quotPrecheck false in
notation "[part|" t "]" => open PartialCorrectness PartialCorrectness.DemonicChoice in t

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
      invariant 1 ≤ n ∧ n ≤ size arr
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
            let left := arr[mind - 1]
            let right := arr[mind]
            arr[mind - 1] := right
            arr[mind] := left
          mind := mind - 1
        n := n + 1
      return
open PartialCorrectness DemonicChoice in
prove_correct insertionSort_part by
  dsimp [insertionSort_part]
  velvet_solve!

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
      invariant 1 ≤ n ∧ n ≤ size arr
      decreasing size arr - n
      do
        let mut mind := n
        while mind ≠ 0
        invariant size arr = arr_size
        invariant mind ≤ n
        decreasing mind
        do
          if arr[mind] < arr[mind - 1] then
            let left := arr[mind - 1]
            let right := arr[mind]
            arr[mind - 1] := right
            arr[mind] := left
          mind := mind - 1
        n := n + 1
      return
open TotalCorrectness DemonicChoice in
prove_correct insertionSort_termination by
  dsimp [insertionSort_termination]
  velvet_solve!


open TotalCorrectness DemonicChoice in
method insertionSort_total
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
      invariant 1 ≤ n ∧ n ≤ size arr
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i] ≤ arr[j]
      invariant toMultiset arr = toMultiset arr₀
      decreasing size arr - n
      do
        let mut mind := n
        while mind ≠ 0
        invariant size arr = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i] ≤ arr[j]
        invariant toMultiset arr = toMultiset arr₀
        decreasing mind
        do
          if arr[mind] < arr[mind - 1] then
            let left := arr[mind - 1]
            let right := arr[mind]
            arr[mind - 1] := right
            arr[mind] := left
          mind := mind - 1
        n := n + 1
      return
open TotalCorrectness DemonicChoice in
prove_correct insertionSort_total by
  have triple_termination := insertionSort_termination_correct arr
  have triple_res := insertionSort_part_correct arr
  exact VelvetM.total_decompose_triple
    (insertionSort_termination arr) (insertionSort_part arr) (insertionSort_total arr)
    (eqx := by rfl) (eqy := by rfl)
    triple_termination
    triple_res
