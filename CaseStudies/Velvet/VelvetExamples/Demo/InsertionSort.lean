----------------------------------------------------
-- Example 1: Velvet basics
----------------------------------------------------

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

section squareRoot

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"
set_option loom.solver "cvc5"
set_option loom.solver.smt.timeout 1

-- (1) Proving things with SMT
-- partial correctness version of square root
method sqrt (x: ℕ) return (res: ℕ)
  ensures res * res ≤ x
  ensures ∀ i, i ≤ res → i * i ≤ x
  ensures ∀ i, i * i ≤ x → i ≤ res
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i  ≤ x
      invariant ∀ j, j < i → j * j ≤ x
      do
        i := i + 1
      return i - 1
prove_correct sqrt by
  loom_solve

-- #eval sqrt 10 |>.extract

set_option loom.solver "grind"

variable [FinEnum α]

method Predicate.toArray (mut s: α -> Bool) return (res: Array α)
  ensures ∀ x, sOld x <-> x ∈ res
  do
    let mut res := #[]
    while ∃ x, s x
    invariant ∀ x, sOld x = true <-> (x ∈ res ∨ s x)
    do
      let x :| s x
      res := res.push x
      s := fun y => if y = x then false else s y
    return res

#eval Predicate.toArray (fun x => x ∈ #[1, 2, (3 : Fin 6)]) |>.extract.1

prove_correct Predicate.toArray by
  loom_solve

end squareRoot

-- (2) Insertion sort
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

attribute [grind] Array.multiset_swap


set_option loom.semantics.termination "partial"
-- set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

--partial correctness version of insertionSort
-- uncomment termination measures for total correctness
method insertionSort
  (mut arr: Array Int) return (u: Unit)
  require 1 ≤ arr.size
  ensures ∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!
  ensures arr.toMultiset = arrOld.toMultiset
  do
    let mut n := 1
    while n ≠ arr.size
    invariant arr.size = arrOld.size
    invariant 1 ≤ n ∧ n ≤ arr.size
    invariant ∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ n - 1 → arr[i]! ≤ arr[j]!
    invariant arr.toMultiset = arrOld.toMultiset
    -- decreasing arr.size - n
    do
      let mut mind := n
      while mind ≠ 0
      invariant arr.size = arrOld.size
      invariant mind ≤ n
      invariant ∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant arr.toMultiset = arrOld.toMultiset
      -- decreasing mind
      do
        if arr[mind]! < arr[mind - 1]! then
          swap! arr[mind - 1]! arr[mind]!
        mind := mind - 1
      n := n + 1 -- try commenting this out for termination
    return

-- Let's test this stuff
extract_program_for insertionSort

-- Determinising the execution
-- #print insertionSortExec

-- Prove decidability as we need to check them
prove_precondition_decidable_for insertionSort
-- #print insertionSortPreDecidable
prove_postcondition_decidable_for insertionSort
derive_tester_for insertionSort

-- (2.1) Doing simple testing
-- See here where the postcondition is violated

run_elab do
  -- Generate random arrays
  let g : Plausible.Gen (_ × Bool) := do
    let arr ← Plausible.SampleableExt.interpSample (Array Int)
    let res := insertionSortTester arr
    pure (arr, res)
  for _ in [1: 500] do
    let res ← Plausible.Gen.run g 10
    unless res.2 do
      IO.println s!"postcondition violated for input {res.1}"
      break

-- (2.2) This just works

set_option maxHeartbeats 1000000

prove_correct insertionSort by
  loom_solve!

end insertionSort
