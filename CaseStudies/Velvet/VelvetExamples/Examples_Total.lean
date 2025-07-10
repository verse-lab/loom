import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std

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

--it is possible to add custom solver hints for Velvet
attribute [local solverHint] TArray.multiSet_swap

--insertion sort implemented in Velvet
method insertionSort_total
  (mut arr: arrInt) return (u: Unit)
  require 1 ≤ size arr
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < size arr → arrNew[i] ≤ arrNew[j]
  ensures toMultiset arr = toMultiset arrNew
  do
    let arr₀ := arr
    let arr_size := size arr
    let mut n := 1
    while n ≠ size arr
    invariant size arr = arr_size
    invariant 1 ≤ n ∧ n ≤ size arr
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i] ≤ arr[j]
    invariant toMultiset arr = toMultiset arr₀
    --explicit decreasing measure for loop termination is required in TotalCorrectness
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
          swap arr[mind - 1] arr[mind]
        mind := mind - 1
      n := n + 1
    return
prove_correct insertionSort_total by
  dsimp [insertionSort_total]
  loom_solve!

end insertionSort

section squareRoot

set_option trace.Loom true

--square root of a non-negative integer implemented in Velvet
method sqrt_total (x: ℕ) return (res: ℕ)
  ensures res * res ≤ x
  ensures ∀ i, i ≤ res → i * i ≤ x
  ensures ∀ i, i * i ≤ x → i ≤ res
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
prove_correct sqrt_total by
  dsimp [sqrt_total]
  loom_solve

--root of power 3 for a non-negative integer implemented in Velvet
method cbrt (x: ℕ) return (res: ℕ)
  ensures res * res * res ≤ x
  ensures ∀ i, i ≤ res → i * i * i ≤ x
  ensures ∀ i, i * i * i ≤ x → i ≤ res
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
  loom_solve
  --SMT failed to discharge one goal, but grind succeeds
  grind

/-
Dafny code for reference below

method sqrt_bn (x: nat, bnd: nat) returns (res: nat)
  requires x < bnd * bnd
  ensures res * res <= x
  ensures forall i: nat :: i <= res ==> i * i <= x
  ensures forall i: nat :: i * i <= x ==> i <= res
{
  var l: nat := 0;
  var r: nat := bnd;
  assert forall i: nat :: i * i <= x ==> i * i < r * r;
  assert forall i: nat :: i * i < r * r ==> 0 < (r - i) * (r + i);
  while 1 < r - l
  invariant l * l <= x
  invariant x < r * r
  invariant forall i: nat :: i <= l ==> i * i <= x
  invariant forall i: nat :: i * i <= x ==> i < r
  {
    var m: nat := (r + l) / 2;
    if m * m <= x {
      l := m;
      assert l <= m < r;
    } else {
      r := m;
      assert l < m <= r;
    }
  }
  return l;
}
-/

--binary search for square root of a non-negative integer implemented in Velvet
method sqrt_bn (x: ℕ) (bnd: ℕ) return (res: ℕ)
  require x < bnd * bnd
  ensures res * res ≤ x
  ensures ∀ i, i ≤ res → i * i ≤ x
  ensures ∀ i, i * i ≤ x → i ≤ res
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
  loom_solve!

end squareRoot
