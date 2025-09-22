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

--method IsGreater(n: int, a: array<int>) returns (result: bool)
    --requires a != null
    --ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]
    --ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]
--{
    --result := true;
    --var i := 0;
    --while i < a.Length
        --invariant 0 <= i <= a.Length
        --invariant result ==> forall k :: 0 <= k < i ==> n > a[k]
        --invariant !result ==> exists k :: 0 <= k < i && n <= a[k]
    --{
        --if n <= a[i] {
            --result := false;
            --break;
        --}
        --i := i + 1;
    --}
--}

method IsGreater
    (n: Int) 
    (a: Array Int) return (result: Bool)
    ensures result = true -> forall i , 0 <= i ∧ i < a.size -> n > a[i]!
    ensures result = false -> exists i , 0 <= i ∧ i < a.size ∧ n <= a[i]!
    do
    let mut result := true
    let mut i := 0
    while i < a.size ∧ result = true
        invariant 0 <= i ∧ i <= a.size
        invariant result = true -> forall k , 0 <= k ∧ k < i -> n > a[k]!
        invariant result = false -> exists k , 0 <= k ∧ k < i ∧ n <= a[k]!
        do
        if n <= a[i]! then
            result := false
        i := i + 1
    return result

prove_correct IsGreater by
  loom_solve
  
