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

method ToLowercase (s: Array Char) return (v: Array Char)
    ensures v.size = s.size
    ensures (forall i, 0 ≤ i ∧ i < s.size → v[i]! = (s[i]!).toLower)
do
    let mut v := Array.replicate s.size ' '
    let mut i := 0
    while i < s.size
        invariant 0 ≤ i ∧ i ≤ s.size
        invariant v.size = s.size
        invariant (forall k, 0 ≤ k ∧ k < i → v[k]! = (s[k]!).toLower)
        done_with (i = s.size)
    do
        let s_char := s[i]!
        v := v.set! i (s_char.toLower)
        i := i + 1
    return v

attribute [local solverHint] Array.size_set Array.size_replicate Array.getElem_setIfInBounds

prove_correct ToLowercase by
  loom_solve
  · simp_all
  · intros k hk hik
    have hks : k < s.size := by grind
    simp_all
    have hkv : k < v.size := by grind
    rw [Array.getElem_setIfInBounds hkv]
    split_ifs with hif
    grind
    have : k < i := by grind
    have : v[k]! = s[k]!.toLower := by
      grind
    simp_all

