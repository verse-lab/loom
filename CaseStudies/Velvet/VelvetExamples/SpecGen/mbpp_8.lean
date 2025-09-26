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

-- MBPP Problem 8: Write a function to find squares of individual elements in a list using lambda function
--
-- Natural language breakdown:
-- 1. We have an input list of natural numbers
-- 2. We want to compute the square (n²) of each individual element in the list
-- 3. The function should return a new list where each element is the square of the corresponding element in the input list
-- 4. The order of elements should be preserved (element at index i in result = square of element at index i in input)
-- 5. The length of the result list should equal the length of the input list
-- 6. For an empty input list, the result should be an empty list
-- 7. The lambda function is an implementation detail - the specification focuses on the mathematical behavior

method SquareElements (nums: List Nat)
  return (squares: List Nat)
  ensures squares.length = nums.length  -- preserve length
  ensures ∀ i < nums.length, squares[i]! = (nums[i]!)^2  -- each element is squared
  ensures nums = [] → squares = []  -- empty case
  do
  pure []  -- placeholder body for type checking

-- Test cases for specification validation
section TestCases

-- Test case 1: Basic list with small numbers
-- Input: [1, 2, 3, 4]
-- Expected: [1, 4, 9, 16]
def testInput1 : List Nat := [1, 2, 3, 4]
def testExpected1 : List Nat := [1, 4, 9, 16]

-- Test case 2: Empty list (edge case)
-- Input: []
-- Expected: []
def testInput2 : List Nat := []
def testExpected2 : List Nat := []

-- Test case 3: Single element list
-- Input: [5]
-- Expected: [25]
def testInput3 : List Nat := [5]
def testExpected3 : List Nat := [25]

-- Test case 4: List with zero and larger numbers
-- Input: [0, 10, 7]
-- Expected: [0, 100, 49]
def testInput4 : List Nat := [0, 10, 7]
def testExpected4 : List Nat := [0, 100, 49]

-- Test case 5: List with repeated elements
-- Input: [3, 3, 2, 3]
-- Expected: [9, 9, 4, 9]
def testInput5 : List Nat := [3, 3, 2, 3]
def testExpected5 : List Nat := [9, 9, 4, 9]

-- Note: The test cases demonstrate the specification's intended behavior:
-- 1. Basic squaring operation with preservation of order and length
-- 2. Proper handling of empty input
-- 3. Single element case
-- 4. Handling of zero (0² = 0) and larger numbers
-- 5. Proper handling of duplicate elements (each occurrence is squared independently)

end TestCases