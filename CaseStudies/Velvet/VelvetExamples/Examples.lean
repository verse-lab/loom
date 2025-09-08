import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

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

-- set_option trace.profiler true
attribute [local solverHint] Array.multiset_swap
attribute [solverHint] Array.size_set_c Array.get_set_c

--partial correctness version of insertionSort
method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < size arr → arrNew[i]! ≤ arrNew[j]!
  ensures toMultiset arr = toMultiset arrNew
  do
    let arr₀ := arr
    let arr_size := arr.size
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arr_size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
    invariant toMultiset arr = toMultiset arr₀
    done_with n = arr.size
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arr_size
      invariant mind ≤ n
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant toMultiset arr = toMultiset arr₀
      done_with mind = 0
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1
    return

extract_program_for insertionSort
prove_precondition_decidable_for insertionSort
prove_postcondition_decidable_for insertionSort by
  (exact (decidable_by_nat_upperbound [(size arr), (size arr)]))
derive_tester_for insertionSort

-- doing simple testing
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    let res := insertionSortTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break

set_option maxHeartbeats 1000000

prove_correct insertionSort by
  loom_solve

end insertionSort

section squareRoot

--partial correctness version of square root
method sqrt (x: ℕ) return (res: ℕ)
  require x > 8
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
      done_with x < i * i
      do
        i := i + 1
      return i - 1

prove_correct sqrt by
  loom_solve!

end squareRoot


section runLengthEncoding

structure Encoding where
  cnt: Nat
  c: Char

variable {velvetString} [arr_inst_int: TArray Char velvetString]
variable {arrEncoding} [arr_encoding_inst: TArray Encoding arrEncoding]

def get_cnt_sum (l: List Encoding) :=
  (l.map (·.cnt)).sum
  


--method RleDecodeIterative<T>(compressed: seq<Run<T>>) returns (decoded: seq<T>)
  --// Preconditions are the same as the specification.
  --requires forall run :: run in compressed ==> run.count > 0
  --// Postconditions guarantee the result is identical to the specification's result.
  --ensures decoded == RleDecode(compressed)
  --ensures |decoded| == SumRunCounts(compressed)
--{
  --decoded := []; // Initialize the result sequence.
  --var i := 0;   // Initialize a loop counter.

  --while i < |compressed|
    --// Loop invariants are properties that must hold at the start of each iteration.
    --// Dafny uses them to prove the loop is correct.
    --invariant 0 <= i <= |compressed|
    --// 1. The index 'i' is always within the valid bounds.

    --invariant decoded == RleDecode(compressed[0..i])
    --// 2. (The Key Invariant): The 'decoded' sequence we have built so far
    --//    is the correct decoding of the runs we have already processed (from 0 to i-1).
  --{
    --var run := compressed[i];

    --// Append the next decoded segment to our result.
    --var segment := RepeatIterative(run.value, run.count);
    --decoded := decoded + segment;

    --i := i + 1;
  --}
--}

method decodeStr (encoded_str: arrEncoding) 
   return (res: velvetString)
   require (forall i, i < size encoded_str -> encoded_str[i].cnt > 0   )
   ensures (size res = get_cnt_sum (TArray.to_list encoded_str) )
     do
       let mut decoded := TArray.replicate 0 default
       let mut i := 0
       while (i < (TArray.size encoded_str))
          invariant 0 <= i ∧ i <= TArray.size encoded_str
          invariant size decoded  = get_cnt_sum (TArray.to_list (TArray.slice 0 i encoded_str))
          done_with i = TArray.size encoded_str
          do
            let elem := encoded_str[0]
            let elem_decoded := TArray.replicate elem.cnt elem.c
            decoded := TArray.append decoded elem_decoded
            i := i + 1
       return decoded


prove_correct decodeStr by
  unfold decodeStr


-- recursive but termination issue
/-
 -method decode (encoded_str: ArrEncoding) return (res: VelvetString)
 -  require (forall i, i < size encoded_str -> encoded_str[i].cnt > 0   )
 -  ensures (size res = get_cnt_sum (TArray.to_list encoded_str) )
 -  do
 -    if size encoded_str = 0 then
 -      return (TArray.replicate 0 default)
 -    else
 -      let rem <- decode (slice 1 ((size encoded_str) - 1) encoded_str)
 -      let fst := encoded_str[0]
 -      return (TArray.append (TArray.replicate fst.cnt fst.c) rem)
 -/

end runLengthEncoding
