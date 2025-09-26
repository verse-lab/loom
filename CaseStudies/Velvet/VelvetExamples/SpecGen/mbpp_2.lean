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

-- MBPP Problem 2: Find the similar elements from the given two tuple lists
--
-- Natural language breakdown:
-- Find elements that appear in both input lists (intersection), returning them
-- in the order they appear in the first list, with duplicates removed.

-- Helper function to capture the expected intersection behavior
def listIntersection {α : Type*} [DecidableEq α] (list1 list2 : List α) : List α :=
  list1.filter (fun elem => elem ∈ list2) |>.dedup

variable {α : Type*} [DecidableEq α]

method SimilarElements (list1 : List α) (list2 : List α)
  return (result: List α)
  ensures ∀ elem, elem ∈ result ↔ (elem ∈ list1 ∧ elem ∈ list2)  -- intersection property
  ensures result = listIntersection list1 list2  -- specific order and deduplication behavior
  ensures result.length ≤ min list1.length list2.length  -- length bound constraint
  ensures (list1 = [] ∨ list2 = []) → result = []  -- empty list handling
  do
  pure []  -- placeholder body for type checking

-- Test cases for specification validation
section TestCases

-- Test case 1: Basic intersection of tuple lists
-- list1 = [(1, 2), (3, 4), (1, 2), (5, 6)]
-- list2 = [(1, 2), (7, 8), (3, 4)]
-- Expected result: [(1, 2), (3, 4)] (no duplicates, order from list1)
def testList1_1 : List (Nat × Nat) := [(1, 2), (3, 4), (1, 2), (5, 6)]
def testList2_1 : List (Nat × Nat) := [(1, 2), (7, 8), (3, 4)]

-- Test case 2: No common elements
-- list1 = [(1, 2), (3, 4)]
-- list2 = [(5, 6), (7, 8)]
-- Expected result: [] (empty list)
def testList1_2 : List (Nat × Nat) := [(1, 2), (3, 4)]
def testList2_2 : List (Nat × Nat) := [(5, 6), (7, 8)]

-- Test case 3: One empty list
-- list1 = [(1, 2), (3, 4)]
-- list2 = []
-- Expected result: [] (empty list)
def testList1_3 : List (Nat × Nat) := [(1, 2), (3, 4)]
def testList2_3 : List (Nat × Nat) := []

-- Test case 4: Both lists empty
-- list1 = []
-- list2 = []
-- Expected result: [] (empty list)
def testList1_4 : List (Nat × Nat) := []
def testList2_4 : List (Nat × Nat) := []

-- Test case 5: All elements are common (with duplicates in first list)
-- list1 = [(1, 2), (3, 4), (1, 2)]
-- list2 = [(3, 4), (1, 2)]
-- Expected result: [(1, 2), (3, 4)] (no duplicates, order from list1)
def testList1_5 : List (Nat × Nat) := [(1, 2), (3, 4), (1, 2)]
def testList2_5 : List (Nat × Nat) := [(3, 4), (1, 2)]

-- Test case 6: Duplicates in both lists
-- list1 = [(1, 2), (3, 4), (1, 2), (5, 6)]
-- list2 = [(1, 2), (1, 2), (3, 4), (7, 8)]
-- Expected result: [(1, 2), (3, 4)] (no duplicates, order from list1)
def testList1_6 : List (Nat × Nat) := [(1, 2), (3, 4), (1, 2), (5, 6)]
def testList2_6 : List (Nat × Nat) := [(1, 2), (1, 2), (3, 4), (7, 8)]

-- Test case 7: Single element lists with match
-- list1 = [(5, 10)]
-- list2 = [(5, 10)]
-- Expected result: [(5, 10)]
def testList1_7 : List (Nat × Nat) := [(5, 10)]
def testList2_7 : List (Nat × Nat) := [(5, 10)]

end TestCases
