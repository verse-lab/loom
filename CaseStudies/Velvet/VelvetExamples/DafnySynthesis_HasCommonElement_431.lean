import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 2
set_option auto.smt.solver.name "cvc5"

method HasCommonElement (a: Array Int) (b: Array Int) return (result: Bool)
    ensures result = true → (∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < b.size ∧ a[i]! = b[j]!)
    ensures result = false → (∀ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < b.size → a[i]! ≠ b[j]!)
do
    let mut result := false
    let mut i := 0
    let mut ii := 0
    let mut jj := 0
    while i < a.size ∧ result = false
        invariant 0 ≤ i ∧ i ≤ a.size
        invariant result = false → (∀ k j, 0 ≤ k ∧ k < i ∧ 0 ≤ j ∧ j < b.size → a[k]! ≠ b[j]!)
        invariant result = true → (0 ≤ ii ∧ ii < a.size ∧ 0 ≤ jj ∧ jj < b.size ∧ a[ii]! = b[jj]!)
        done_with (i = a.size ∨ result = true)
    do
        let mut j := 0
        while j < b.size ∧ result = false
            invariant 0 ≤ j ∧ j ≤ b.size
            invariant result = false → (∀ k, 0 ≤ k ∧ k < j → a[i]! ≠ b[k]!)
            invariant result = true → (0 ≤ ii ∧ ii < a.size ∧ 0 ≤ jj ∧ jj < b.size ∧ a[ii]! = b[jj]!)
            done_with (j = b.size ∨ result = true)
        do
            if a[i]! = b[j]! then
                result := true
                ii := i
                jj := j
            j := j + 1
        i := i + 1
    return result

prove_correct HasCommonElement by
  loom_solve
