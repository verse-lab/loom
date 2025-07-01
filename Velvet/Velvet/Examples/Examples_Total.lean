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

open TotalCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

attribute [solverHint] TArray.get_set TArray.size_set

section insertionSort

/-

Dafny code below for reference

method insertionSort(arr: array<int>)
  modifies arr
  ensures forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures multiset(arr[..]) == old(multiset(arr[..]))
{
  if arr.Length <= 1 {
    return;
  }
  var n := 1;
  while n != arr.Length
  invariant 0 <= n <= arr.Length
  invariant forall i, j :: 0 <= i < j <= n - 1 ==> arr[i] <= arr[j]
  invariant multiset(arr[..]) == old(multiset(arr[..]))
  {
    var mind := n;
    while mind != 0
    invariant 0 <= mind <= n
    invariant multiset(arr[..]) == old(multiset(arr[..]))
    invariant forall i, j :: 0 <= i < j <= n && (j != mind)==> arr[i] <= arr[j]
    {
      if arr[mind] <= arr[mind - 1] {
        arr[mind], arr[mind - 1] := arr[mind - 1], arr[mind];
      }
      mind := mind - 1;
    }
    n := n + 1;
  }
}
-/

variable {arrInt} [arr_inst_int: TArray Int arrInt]
variable {arrNat} [arr_inst: TArray Nat arrNat]

-- set_option trace.profiler true
attribute [local solverHint] TArray.multiSet_swap

method insertionSort
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
prove_correct insertionSort by
  dsimp [insertionSort]
  velvet_solve!

end insertionSort

section squareRoot

set_option trace.Loom true

method sqrt (x: ℕ) return (res: ℕ)
  ensures res * res ≤ x ∧ ∀ i, i ≤ res → i * i ≤ x
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i ≤ x
      invariant ∀ j, j < i → j * j ≤ x
      decreasing x + 8 - i
      do
        i := i + 1
      return i - 1
prove_correct sqrt by
  dsimp [sqrt]
  velvet_solve

method cbrt (x: ℕ) return (res: ℕ)
  ensures res * res * res ≤ x ∧ ∀ i, i ≤ res → i * i * i ≤ x
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i * i ≤ x
      invariant ∀ j, j < i → j * j * j ≤ x
      decreasing x + 8 - i
      do
        i := i + 1
      return i - 1
prove_correct cbrt by
  dsimp [cbrt]
  velvet_solve
  grind

method sqrt_bn (x: ℕ) (bnd: ℕ) return (res: ℕ)
  require x < bnd * bnd
  ensures res * res ≤ x ∧ ∀ i, i ≤ res → i * i ≤ x
  do
    let mut l := 0
    let mut r := bnd
    while 1 < r - l
    invariant l * l ≤ x
    invariant x < r * r
    invariant ∀ i, i ≤ l → i * i ≤ x
    decreasing r - l
    do
      let m := (r + l) / 2
      if m * m ≤ x then
        l := m
      else
        r := m
    return l
prove_correct sqrt_bn by
  dsimp [sqrt_bn]
  velvet_solve!

end squareRoot
