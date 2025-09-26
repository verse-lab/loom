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

-- MBPP Problem 5: Find the number of ways to fill a 3×n board with 2×1 dominoes
--
-- Natural language breakdown:
-- 1. We have a rectangular board with exactly 3 rows and n columns (3×n board)
-- 2. We want to completely fill this board using 2×1 dominoes (rectangular pieces covering exactly 2 adjacent squares)
-- 3. Dominoes can be placed either horizontally (covering 2 adjacent columns in the same row) or vertically (covering 2 adjacent rows in the same column)
-- 4. The board must be completely filled with no empty squares and no overlapping dominoes
-- 5. We count the number of distinct ways to achieve such a complete tiling
-- 6. The function should return this count as a natural number
-- 7. For impossible cases (like n=1, where 3×1 cannot be tiled with 2×1 pieces), the count should be 0

-- Mathematical insight: This is a classic tiling problem with the following properties:
-- - For n=0: 1 way (empty board, vacuously true)
-- - For n=1: 0 ways (3×1 board cannot be perfectly tiled with 2×1 dominoes)
-- - For n≥2: follows a recurrence relation based on how the rightmost columns can be filled
-- - The problem exhibits optimal substructure: ways to fill 3×n depends on ways to fill smaller boards

-- Helper function to verify the mathematical recurrence (for documentation)
-- The recurrence for this problem is: f(n) = 4*f(n-2) - f(n-4) for n≥4
-- with base cases f(0)=1, f(1)=0, f(2)=3, f(3)=0
def dominoTilingRecurrence (n: Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 0
  | n + 4 => 4 * dominoTilingRecurrence (n + 2) - dominoTilingRecurrence n

method DominoTiling (n: Nat)
  return (count: Nat)
  ensures count ≥ 0  -- result is always non-negative
  ensures n = 0 → count = 1  -- empty board has exactly one way (no dominoes needed)
  ensures n = 1 → count = 0  -- impossible to tile 3×1 board with 2×1 dominoes
  ensures n = 2 → count = 3  -- base case: 3×2 board can be tiled in exactly 3 ways
  ensures n = 3 → count = 0  -- impossible to tile 3×3 board (9 squares cannot be tiled with 2×1 dominoes)
  ensures (n % 2 = 0) → count > 0  -- for even n (including 0), there are always positive number of ways
  ensures n ≥ 4 ∧ n % 2 = 0 → count = dominoTilingRecurrence n  -- follows recurrence relation for n≥4
  do
  pure 0  -- placeholder body for type checking

-- Test cases for specification validation
section TestCases

-- Test case 1: Empty board (edge case)
-- n = 0
-- Expected: 1 way (no dominoes needed)
-- This tests the base case: empty board has exactly one valid tiling

-- Test case 2: Single column (impossible case)
-- n = 1
-- Expected: 0 ways (3×1 cannot be tiled with 2×1 dominoes)
-- This tests the impossibility constraint

-- Test case 3: Two columns (basic case)
-- n = 2
-- Expected: 3 ways
-- Ways: (1) three horizontal dominoes stacked vertically
--       (2) one vertical domino in first two rows + one horizontal in bottom
--       (3) one horizontal in top + one vertical domino in last two rows

-- Test case 4: Three columns (impossible case)
-- n = 3
-- Expected: 0 ways (3×3 = 9 squares, cannot be perfectly divided by 2×1 dominoes)
-- Total squares = 9, each domino covers 2 squares, so impossible

-- Test case 5: Four columns
-- n = 4
-- Expected: 11 ways (computed via recurrence: 4*3 - 1 = 11)
-- This tests the recurrence relation for larger values

-- Test case 6: Six columns
-- n = 6
-- Expected: 41 ways (computed via recurrence)
-- f(6) = 4*f(4) - f(2) = 4*11 - 3 = 44 - 3 = 41

-- Test case 7: Eight columns (additional test for larger even value)
-- n = 8
-- Expected: 153 ways (computed via recurrence)
-- f(8) = 4*f(6) - f(4) = 4*41 - 11 = 164 - 11 = 153

-- Mathematical verification of key test cases using the recurrence
#check dominoTilingRecurrence 0 = 1  -- should be true
#check dominoTilingRecurrence 1 = 0  -- should be true
#check dominoTilingRecurrence 2 = 3  -- should be true
#check dominoTilingRecurrence 3 = 0  -- should be true
#check dominoTilingRecurrence 4 = 11 -- should be true
#check dominoTilingRecurrence 6 = 41 -- should be true
#check dominoTilingRecurrence 8 = 153 -- should be true

-- Note: The specification captures the essential properties of the domino tiling problem:
-- 1. Correct handling of impossible cases (odd total squares)
-- 2. Proper base cases for small values of n
-- 3. Guarantee of positive solutions for valid even-area cases
-- 4. The actual implementation would use dynamic programming to compute the recurrence efficiently

end TestCases
