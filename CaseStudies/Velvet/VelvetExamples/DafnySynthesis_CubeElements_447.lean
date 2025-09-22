import Auto

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

--method CubeElements(a: array<int>) returns (cubed: array<int>)
--    ensures cubed.Length == a.Length
--    ensures forall i :: 0 <= i < a.Length ==> cubed[i] == a[i] * a[i] * a[i]
--{
--    var cubedArray := new int[a.Length];
--    for i := 0 to a.Length
--        invariant 0 <= i <= a.Length
--        invariant cubedArray.Length == a.Length
--        invariant forall k :: 0 <= k < i ==> cubedArray[k] == a[k] * a[k] * a[k]
--    {
--        cubedArray[i] := a[i] * a[i] * a[i];
--    }
--    return cubedArray;
--}

method CubeElements (a: Array Int) return (cubed: Array Int)
    ensures cubed.size = a.size
    ensures ∀ i, 0 ≤ i ∧ i < a.size → cubed[i]! = a[i]! * a[i]! * a[i]!
    do
    let mut cubedArray := Array.replicate a.size 0
    let mut i := 0
    while i < a.size
    invariant cubedArray.size = a.size
    invariant 0 ≤ i ∧ i ≤ a.size
    invariant ∀ k, 0 ≤ k ∧ k < i → cubedArray[k]! = a[k]! * a[k]! * a[k]!
    do
        cubedArray := cubedArray.set! i (a[i]! * a[i]! * a[i]!)
        i := i + 1
    return cubedArray

attribute [local solverHint] Array.size_replicate Array.size_set 

prove_correct CubeElements by
  loom_solve <;> simp_all
  intros k hik
  unfold Array.setIfInBounds
  simp_all
  have : k < a.size := by
    grind
  by_cases hik' : i = k  <;> simp_all
  have hkLtI: k < i := by grind
  have inv' : cubedArray[k]! = a[k]! * a[k]! * a[k]! := by 
    grind
  have hk' : k < cubedArray.size := by grind
  simp_all
