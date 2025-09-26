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

-- MBPP Problem 1: Find minimum cost path from (0,0) to (m,n) in cost matrix
--
-- Natural language breakdown:
-- 1. We have a 2D cost matrix where each cell contains a non-negative cost value
-- 2. We start at position (0, 0) and want to reach position (m, n)
-- 3. MOVEMENT CONSTRAINT: We can only move right (increase column) or down (increase row)
--    This is a standard constraint in dynamic programming path problems to ensure
--    that paths are acyclic and the problem has optimal substructure
-- 4. The cost of a path is the sum of all costs of cells in the path including start and end
-- 5. We want to find the minimum possible total cost among all valid paths
-- 6. The function should return this minimum cost

-- Helper definition for valid path (only right and down moves allowed)
def isValidPath (path: List (Nat × Nat)) (startRow startCol endRow endCol: Nat) : Prop :=
  path.length > 0 ∧
  path.head? = some (startRow, startCol) ∧
  path.getLast? = some (endRow, endCol) ∧
  ∀ i, i + 1 < path.length →
    let curr := path[i]!
    let next := path[i + 1]!
    (next.1 = curr.1 ∧ next.2 = curr.2 + 1) ∨  -- right move
    (next.1 = curr.1 + 1 ∧ next.2 = curr.2)     -- down move

-- Helper definition for path cost calculation
-- Assumes all coordinates in path are valid for the given cost matrix
-- (this should be guaranteed by isValidPath when used properly)
def pathCost (cost: Array (Array Nat)) (path: List (Nat × Nat)) : Nat :=
  path.foldl (fun acc (i, j) =>
    -- Bounds checking could be added here for additional safety:
    -- if h : i < cost.size ∧ j < cost[i]!.size then acc + cost[i][j] else acc
    -- For now, we rely on preconditions ensuring valid bounds
    acc + cost[i]![j]!) 0

method MinCostPath (cost: Array (Array Nat)) (m: Nat) (n: Nat)
  return (minCost: Nat)
  require cost.size > 0
  require ∀ i < cost.size, cost[i]!.size > 0
  require ∀ i < cost.size, cost[i]!.size = cost[0]!.size  -- rectangular matrix
  require m < cost.size
  require n < cost[0]!.size
  ensures ∃ path, isValidPath path 0 0 m n ∧ pathCost cost path = minCost  -- achievable minimum
  ensures ∀ path, isValidPath path 0 0 m n → pathCost cost path ≥ minCost  -- truly minimum
  ensures (m = 0 ∧ n = 0) → minCost = cost[0]![0]!  -- edge case: start equals end
  do
  pure 0  -- placeholder body for type checking

-- Test cases for specification validation
section TestCases

-- Test case 1: Simple 2x2 matrix
-- cost = [[1, 3], [1, 5]]
-- Expected minimum path: (0,0) → (1,0) → (1,1) with cost 1+1+5 = 7
def testMatrix1 : Array (Array Nat) := #[#[1, 3], #[1, 5]]

-- Test case 2: Single cell matrix (edge case: start equals end, m=0, n=0)
-- cost = [[5]]
-- Expected minimum path: (0,0) with cost 5
-- This tests the edge case postcondition: (m = 0 ∧ n = 0) → minCost = cost[0]![0]!
def testMatrix2 : Array (Array Nat) := #[#[5]]

-- Test case 3: 3x3 matrix with clear optimal path
-- cost = [[1, 2, 3], [4, 8, 2], [1, 5, 3]]
-- Optimal path: (0,0) → (0,1) → (0,2) → (1,2) → (2,2) with cost 1+2+3+2+3 = 11
def testMatrix3 : Array (Array Nat) := #[#[1, 2, 3], #[4, 8, 2], #[1, 5, 3]]

-- Note: Formal verification of test cases would require additional array manipulation theorems
-- The test cases demonstrate the specification's intended behavior on concrete inputs

end TestCases
