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

method IsSorted(a: Array Int) return (sorted: Bool)
    require a.size > 0
    ensures sorted ↔ (∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!)
do
    let mut sorted := true
    let mut i := 0
    while i < a.size - 1 ∧ sorted
        invariant 0 ≤ i ∧ i ≤ a.size - 1
        invariant sorted = true → (∀ k, 0 ≤ k ∧ k < i → a[k]! ≤ a[k+1]!)
        invariant sorted = false → ∃ k, 0 ≤ k ∧ k < a.size - 1 ∧ a[k]! > a[k+1]!
        done_with (i = a.size - 1 ∨ sorted = false)
    do
        if a[i]! > a[i+1]! then
            sorted := false
        i := i + 1
    return sorted

-- Helper function that proves transitivity recursively
def chain_le (a : Array Int) (h_adjacent : ∀ k, 0 ≤ k ∧ k < a.size - 1 → a[k]! ≤ a[k+1]!)
    (i j : Nat) (h_i_ge : 0 ≤ i) (h_i_lt_j : i < j) (h_j_lt_size : j < a.size) : a[i]! ≤ a[j]! :=
  if h : j = i + 1 then by
    -- Base case: adjacent elements
    rw [h]
    exact h_adjacent i ⟨h_i_ge, by omega⟩
  else by
    -- Recursive case: use transitivity
    have h_next : i + 1 < j := by omega
    have h_step1 := h_adjacent i ⟨h_i_ge, by omega⟩
    have h_step2 := chain_le a h_adjacent (i + 1) j (by omega) h_next (by omega)
    exact le_trans h_step1 h_step2
termination_by j - i

-- Main helper lemma
lemma adjacent_to_global_sorted (a : Array Int) :
    (∀ k, 0 ≤ k ∧ k < a.size - 1 → a[k]! ≤ a[k+1]!) →
    (∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!) := by
  intro h_adjacent i j h_bounds
  have ⟨h_i_ge, h_i_lt_j, h_j_lt_size⟩ := h_bounds
  exact chain_le a h_adjacent i j h_i_ge h_i_lt_j h_j_lt_size

attribute [local solverHint] adjacent_to_global_sorted

prove_correct IsSorted by
  loom_solve
