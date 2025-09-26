import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

-- MBPP Problem 10: Write a function to get the n smallest items from a dataset
--
-- Natural language breakdown:
-- 1. We have a dataset (list) of comparable natural numbers that can be ordered
-- 2. We want to extract exactly n elements from this dataset
-- 3. These n elements should be the smallest according to the natural ordering
-- 4. The function should return a list containing these n smallest elements
-- 5. If n is greater than the dataset size, return all elements (sorted)
-- 6. If n is 0, return an empty list
-- 7. If the dataset is empty, return an empty list regardless of n
-- 8. The returned elements should be in sorted order (smallest to largest)
-- 9. If there are duplicate values, they should be preserved in the result
-- 10. The original dataset should not be modified (functional approach)

-- Helper function to check if a list is sorted in ascending order
def isSorted (l : List Nat) : Bool :=
  (l.zip l.tail).all fun (a, b) => a ≤ b

-- Concrete function to get n smallest elements from a dataset
def getNSmallestHelper (dataset : List Nat) (n : Nat) : List Nat :=
  let sorted := dataset.mergeSort (· ≤ ·)
  sorted.take n

method getNSmallest (dataset : List Nat) (n : Nat)
  return (result : List Nat)
  ensures result = getNSmallestHelper dataset n  -- result is exactly what our helper function produces
  ensures result.length ≤ n  -- result size is at most n
  ensures result.length ≤ dataset.length  -- result size is at most dataset size
  ensures ∀ x ∈ result, x ∈ dataset  -- all result elements come from dataset
  ensures isSorted result  -- result is sorted in ascending order
  do
  pure (getNSmallestHelper dataset n)

-- Test cases for specification validation
section TestCases

-- Test case 1: Basic case with distinct elements
-- dataset = [7, 10, 4, 3, 20, 15], n = 3
-- Expected result: [3, 4, 7] (3 smallest elements in sorted order)
def testDataset1 : List Nat := [7, 10, 4, 3, 20, 15]
-- getNSmallest testDataset1 3 should return [3, 4, 7]

-- Test case 2: n greater than dataset size
-- dataset = [5, 2, 8], n = 5
-- Expected result: [2, 5, 8] (all elements in sorted order)
def testDataset2 : List Nat := [5, 2, 8]
-- getNSmallest testDataset2 5 should return [2, 5, 8]

-- Test case 3: n equals 0
-- dataset = [1, 2, 3], n = 0
-- Expected result: [] (empty list)
def testDataset3 : List Nat := [1, 2, 3]
-- getNSmallest testDataset3 0 should return []

-- Test case 4: Empty dataset
-- dataset = [], n = 3
-- Expected result: [] (empty list)
def testDataset4 : List Nat := []
-- getNSmallest testDataset4 3 should return []

-- Test case 5: Dataset with duplicates
-- dataset = [4, 1, 4, 2, 4, 1], n = 4
-- Expected result: [1, 1, 2, 4] (4 smallest including duplicates)
def testDataset5 : List Nat := [4, 1, 4, 2, 4, 1]
-- getNSmallest testDataset5 4 should return [1, 1, 2, 4]

-- Test case 6: Single element dataset
-- dataset = [42], n = 1
-- Expected result: [42]
def testDataset6 : List Nat := [42]
-- getNSmallest testDataset6 1 should return [42]

-- Test case 7: All elements equal
-- dataset = [5, 5, 5, 5], n = 2
-- Expected result: [5, 5] (any 2 elements, all equal)
def testDataset7 : List Nat := [5, 5, 5, 5]
-- getNSmallest testDataset7 2 should return [5, 5]

-- Test case 8: Large n with small dataset
-- dataset = [100], n = 10
-- Expected result: [100] (only available element)
def testDataset8 : List Nat := [100]
-- getNSmallest testDataset8 10 should return [100]

-- Test case 9: n equals dataset size
-- dataset = [9, 1, 5], n = 3
-- Expected result: [1, 5, 9] (all elements sorted)
def testDataset9 : List Nat := [9, 1, 5]
-- getNSmallest testDataset9 3 should return [1, 5, 9]

-- Test case 10: Already sorted dataset
-- dataset = [1, 2, 3, 4, 5], n = 3
-- Expected result: [1, 2, 3] (first 3 elements)
def testDataset10 : List Nat := [1, 2, 3, 4, 5]
-- getNSmallest testDataset10 3 should return [1, 2, 3]

-- Test case 11: Reverse sorted dataset
-- dataset = [10, 8, 6, 4, 2], n = 3
-- Expected result: [2, 4, 6] (3 smallest elements in sorted order)
def testDataset11 : List Nat := [10, 8, 6, 4, 2]
-- getNSmallest testDataset11 3 should return [2, 4, 6]

-- Test case 12: Mixed duplicates and unique values
-- dataset = [3, 1, 3, 2, 1, 4, 2], n = 5
-- Expected result: [1, 1, 2, 2, 3] (5 smallest including duplicates)
def testDataset12 : List Nat := [3, 1, 3, 2, 1, 4, 2]
-- getNSmallest testDataset12 5 should return [1, 1, 2, 2, 3]

end TestCases