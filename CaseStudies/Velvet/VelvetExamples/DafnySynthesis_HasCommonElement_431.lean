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

--method HasCommonElement(a: array<int>, b: array<int>) returns (result: bool)
    --requires a != null && b != null
    --ensures result ==> exists i, j :: 0 <= i < a.Length && 0 <= j < b.Length && a[i] == b[j]
    --ensures !result ==> forall i, j :: 0 <= i < a.Length && 0 <= j < b.Length ==> a[i] != b[j]
--{
    --result := false;
    --for i := 0 to a.Length
        --invariant 0 <= i <= a.Length
        --invariant !result ==> forall k, j :: 0 <= k < i && 0 <= j < b.Length ==> a[k] != b[j]
    --{
        --for j := 0 to b.Length
            --invariant 0 <= j <= b.Length
            --invariant !result ==> forall k :: 0 <= k < j ==> a[i] != b[k]
        --{
            --if a[i] == b[j] {
                --result := true;
                --return;
            --}
        --}
    --}
--}

method HasCommonElement(a: Array Int) (b: Array Int) return (result: Bool)
    ensures result = true -> ∃ i, (∃ j , 0 <= i ∧ i  < a.size ∧  0 <= j ∧ j < b.size ∧ a[i]! = b[j]!)
    ensures result = false ->  forall i j , 0 <= i ∧ i  < a.size ∧ 0 <= j ∧ j < b.size -> a[i]! != b[j]!
    do
    let mut result := false
    let mut i := 0
    while i < a.size
        invariant 0 <= i ∧ i <= a.size
        invariant result = false ->  forall k j , 0 <= k ∧ k  < i ∧ 0 <= j ∧ j < b.size -> a[k]! != b[j]!
        do 
        let mut j := 0
        while j < b.size ∧ result = false
            invariant 0 <= j ∧ j <= b.size
            invariant result = false -> forall k , 0 <= k ∧ k < j -> a[i]! != b[k]!
            do
            if a[i]! = b[j]! then
                result := true
            j := j + 1
        i := i + 1
    return result

prove_correct HasCommonElement by
  unfold HasCommonElement 
  loom_solve
  sorry


  
  
/- #eval (HasCommonElement #[1,2,3] #[4,5,9] ).run -/
