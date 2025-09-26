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

-- MBPP Problem 4: Write a function to find the largest integers from a given list of numbers using heap queue algorithm.
--
-- Specification: Find the maximum value from a non-empty list of integers.
-- The "heap queue algorithm" is an implementation detail - we focus on correctness.
-- Interpretation: "largest integers" refers to the single maximum value in the list.

method FindLargestInteger (numbers: List Int)
  return (largest: Int)
  require numbers.length > 0  -- Non-empty list required
  ensures largest ∈ numbers  -- Result must be in the original list
  ensures ∀ x ∈ numbers, x ≤ largest  -- Result is greater than or equal to all elements
  do
  pure 0  -- placeholder body for type checking

-- Test cases for specification validation
section TestCases

-- Test case 1: Simple positive integers
-- Input: [1, 3, 5, 2, 4]
-- Expected: 5 (largest element)
def testList1 : List Int := [1, 3, 5, 2, 4]

-- Test case 2: List with negative numbers
-- Input: [-10, -3, -5, -1]
-- Expected: -1 (largest element, least negative)
def testList2 : List Int := [-10, -3, -5, -1]

-- Test case 3: Mixed positive and negative numbers
-- Input: [-2, 5, -8, 10, 3]
-- Expected: 10 (largest element)
def testList3 : List Int := [-2, 5, -8, 10, 3]

-- Test case 4: Single element list (edge case)
-- Input: [42]
-- Expected: 42 (only element, hence largest)
def testList4 : List Int := [42]

-- Test case 5: List with zeros and negative numbers
-- Input: [0, -5, -2, 0, -1]
-- Expected: 0 (largest element)
def testList5 : List Int := [0, -5, -2, 0, -1]

-- Test case 6: List with duplicate maximum values
-- Input: [3, 7, 1, 7, 5]
-- Expected: 7 (largest element, appears multiple times)
def testList6 : List Int := [3, 7, 1, 7, 5]

-- Test case 7: Large numbers
-- Input: [1000, 500, 2000, 1500]
-- Expected: 2000 (largest element)
def testList7 : List Int := [1000, 500, 2000, 1500]

-- Verification that our specification captures the correct behavior:
-- 1. Requires non-empty input list (empty list case handled by precondition)
-- 2. Guarantees result is an element from the input list
-- 3. Guarantees result is greater than or equal to all elements in the list
-- 4. Works correctly with positive, negative, and zero values
-- 5. Handles duplicate maximum values correctly
-- 6. Works for single element lists
-- 7. The implementation can use any algorithm (heap queue or otherwise) as long as it meets the specification

end TestCases