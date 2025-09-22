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

-- Helper function to compute product of a finite set of integers
def setProduct (s : Finset Int) : Int :=
  s.prod id

-- Define the set of unique elements from array slice
def uniqueElements (a : Array Int) (i : Nat) : Finset Int :=
  (Finset.range i).image (fun k => a[k]!)

-- Helper function to check if element is already seen
def elementInArray (arr : Array Int) (elem : Int) (upTo : Nat) : Bool :=
  if upTo = 0 then false
  else if arr[upTo - 1]! = elem then true
  else elementInArray arr elem (upTo - 1)

-- Lemma connecting elementInArray with Finset membership
lemma elementInArray_iff_mem (arr : Array Int) (elem : Int) (i : Nat) :
  elementInArray arr elem i = true ↔ elem ∈ uniqueElements arr i := by
  sorry

-- Lemma about adding new element to unique set
lemma uniqueElements_step (arr : Array Int) (i : Nat) (h : i < arr.size) :
  uniqueElements arr (i + 1) =
    if arr[i]! ∈ uniqueElements arr i
    then uniqueElements arr i
    else uniqueElements arr i ∪ {arr[i]!} := by
  sorry

-- Lemma about set product when adding new element
lemma setProduct_insert (s : Finset Int) (x : Int) (h : x ∉ s) :
  setProduct (s ∪ {x}) = setProduct s * x := by
  sorry

attribute [local solverHint] elementInArray_iff_mem uniqueElements_step setProduct_insert

method UniqueProduct(arr: Array Int) return (product: Int)
    require arr.size ≥ 0
    ensures product = setProduct (uniqueElements arr arr.size)
do
    let mut p := 1
    let mut i := 0

    while i < arr.size
        invariant 0 ≤ i ∧ i ≤ arr.size
        invariant p = setProduct (uniqueElements arr i)
        done_with (i = arr.size)
    do
        if ¬elementInArray arr arr[i]! i then
            p := p * arr[i]!
        i := i + 1

    return p

prove_correct UniqueProduct by
  loom_solve
