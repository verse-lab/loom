import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

-- MBPP Problem 12: Sort a given matrix in ascending order according to the sum of its rows
--
-- Natural language breakdown:
-- 1. Given a matrix represented as an array of arrays (rows)
-- 2. Calculate the sum of elements in each row
-- 3. Sort the rows based on these sums in ascending order
-- 4. Rows with smaller sums should appear before rows with larger sums
-- 5. If two rows have the same sum, preserve their relative order (stable sort)
-- 6. Return the matrix with rows reordered according to their sums
-- 7. The individual elements within each row remain in their original positions
-- 8. Empty rows should have sum 0 and sort accordingly
-- 9. Empty matrix should remain empty

-- Helper function to calculate the sum of elements in a row
def rowSum (row: Array Nat) : Nat :=
  row.foldl (· + ·) 0

-- Helper function to check if a matrix is sorted by row sums in ascending order
def isSortedByRowSum (matrix: Array (Array Nat)) : Bool :=
  let sums := matrix.map rowSum
  (sums.toList.zip sums.toList.tail).all fun (a, b) => a ≤ b

-- Concrete function to sort matrix by row sums
def sortMatrixByRowSum (matrix: Array (Array Nat)) : Array (Array Nat) :=
  -- Create pairs of (row, sum) for sorting
  let rowsWithSums := matrix.toList.map fun row => (row, rowSum row)
  -- Sort by sum (second element of pair)
  let sortedPairs := rowsWithSums.mergeSort fun (_, sum1) (_, sum2) => sum1 ≤ sum2
  -- Extract just the rows
  Array.mk (sortedPairs.map (·.1))

method SortMatrixByRowSum (matrix: Array (Array Nat))
  return (result: Array (Array Nat))
  ensures result = sortMatrixByRowSum matrix
  ensures result.size = matrix.size  -- Same number of rows
  ensures ∀ i < result.size, result[i]!.size = matrix[i]!.size  -- Row sizes preserved
  ensures isSortedByRowSum result  -- Result is sorted by row sums
  ensures ∀ row, row ∈ result.toList ↔ row ∈ matrix.toList  -- Same rows, just reordered
  do
  pure (sortMatrixByRowSum matrix)

-- Test cases for specification validation
section TestCases

-- Test case 1: Simple 3x3 matrix with different row sums
-- matrix = [[1, 2, 3], [7, 8, 9], [4, 5, 6]]
-- Row sums: [6, 24, 15]
-- Expected result: [[1, 2, 3], [4, 5, 6], [7, 8, 9]] (sorted by sums: 6, 15, 24)
def testMatrix1 : Array (Array Nat) := #[#[1, 2, 3], #[7, 8, 9], #[4, 5, 6]]
-- sortMatrixByRowSum testMatrix1 should return #[#[1, 2, 3], #[4, 5, 6], #[7, 8, 9]]

-- Test case 2: Matrix with equal row sums (stability test)
-- matrix = [[1, 2], [3, 0], [2, 1]]
-- Row sums: [3, 3, 3] (all equal)
-- Expected result: [[1, 2], [3, 0], [2, 1]] (original order preserved)
def testMatrix2 : Array (Array Nat) := #[#[1, 2], #[3, 0], #[2, 1]]
-- sortMatrixByRowSum testMatrix2 should return #[#[1, 2], #[3, 0], #[2, 1]]

-- Test case 3: Matrix with some zero rows
-- matrix = [[0, 0, 0], [1, 2, 3], [0, 0, 1]]
-- Row sums: [0, 6, 1]
-- Expected result: [[0, 0, 0], [0, 0, 1], [1, 2, 3]] (sorted by sums: 0, 1, 6)
def testMatrix3 : Array (Array Nat) := #[#[0, 0, 0], #[1, 2, 3], #[0, 0, 1]]
-- sortMatrixByRowSum testMatrix3 should return #[#[0, 0, 0], #[0, 0, 1], #[1, 2, 3]]

-- Test case 4: Single row matrix
-- matrix = [[5, 10, 15]]
-- Row sums: [30]
-- Expected result: [[5, 10, 15]] (unchanged, single row)
def testMatrix4 : Array (Array Nat) := #[#[5, 10, 15]]
-- sortMatrixByRowSum testMatrix4 should return #[#[5, 10, 15]]

-- Test case 5: Empty matrix
-- matrix = []
-- Row sums: []
-- Expected result: [] (unchanged, empty)
def testMatrix5 : Array (Array Nat) := #[]
-- sortMatrixByRowSum testMatrix5 should return #[]

-- Test case 6: Matrix with single element rows
-- matrix = [[5], [2], [8], [1]]
-- Row sums: [5, 2, 8, 1]
-- Expected result: [[1], [2], [5], [8]] (sorted by sums: 1, 2, 5, 8)
def testMatrix6 : Array (Array Nat) := #[#[5], #[2], #[8], #[1]]
-- sortMatrixByRowSum testMatrix6 should return #[#[1], #[2], #[5], #[8]]

-- Test case 7: Matrix with empty rows
-- matrix = [[], [1, 2], []]
-- Row sums: [0, 3, 0]
-- Expected result: [[], [], [1, 2]] (empty rows first, then row with sum 3)
def testMatrix7 : Array (Array Nat) := #[#[], #[1, 2], #[]]
-- sortMatrixByRowSum testMatrix7 should return #[#[], #[], #[1, 2]]

-- Test case 8: Already sorted matrix
-- matrix = [[1], [1, 1], [1, 1, 1]]
-- Row sums: [1, 2, 3]
-- Expected result: [[1], [1, 1], [1, 1, 1]] (unchanged, already sorted)
def testMatrix8 : Array (Array Nat) := #[#[1], #[1, 1], #[1, 1, 1]]
-- sortMatrixByRowSum testMatrix8 should return #[#[1], #[1, 1], #[1, 1, 1]]

-- Test case 9: Reverse sorted matrix
-- matrix = [[10, 10, 10], [5, 5], [1]]
-- Row sums: [30, 10, 1]
-- Expected result: [[1], [5, 5], [10, 10, 10]] (sorted by sums: 1, 10, 30)
def testMatrix9 : Array (Array Nat) := #[#[10, 10, 10], #[5, 5], #[1]]
-- sortMatrixByRowSum testMatrix9 should return #[#[1], #[5, 5], #[10, 10, 10]]

-- Test case 10: Large numbers and mixed row sizes
-- matrix = [[100], [1, 1, 1], [50, 50]]
-- Row sums: [100, 3, 100]
-- Expected result: [[1, 1, 1], [100], [50, 50]] (sorted by sums: 3, 100, 100 - preserving order for ties)
def testMatrix10 : Array (Array Nat) := #[#[100], #[1, 1, 1], #[50, 50]]
-- sortMatrixByRowSum testMatrix10 should return #[#[1, 1, 1], #[100], #[50, 50]]

-- Test case 11: Matrix with duplicate rows
-- matrix = [[2, 3], [1, 4], [2, 3]]
-- Row sums: [5, 5, 5] (all same)
-- Expected result: [[2, 3], [1, 4], [2, 3]] (original order preserved - stable sort)
def testMatrix11 : Array (Array Nat) := #[#[2, 3], #[1, 4], #[2, 3]]
-- sortMatrixByRowSum testMatrix11 should return #[#[2, 3], #[1, 4], #[2, 3]]

end TestCases