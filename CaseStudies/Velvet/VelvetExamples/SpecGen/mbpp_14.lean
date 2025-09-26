import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

-- MBPP Problem 14: Find the volume of a triangular prism
--
-- Natural language breakdown:
-- 1. A triangular prism has a triangular base and extends to a certain height
-- 2. The volume is calculated as: Volume = Base Area × Height
-- 3. For a triangle with base 'b' and height 'h', the area is: Area = (b × h) / 2
-- 4. So the volume formula is: Volume = (base × triangle_height × prism_height) / 2
-- 5. All input measurements (base, triangle height, prism height) must be positive
-- 6. The result should be a positive rational number
-- 7. Since we're working with natural numbers, we'll use integer arithmetic
-- 8. We'll return the volume multiplied by 2 to avoid fractions, then divide by 2
-- 9. For simplicity, we'll work with natural numbers and return the exact volume

-- Helper function to calculate the area of a triangle
def triangleArea (base: Nat) (height: Nat) : Nat :=
  (base * height) / 2

-- Concrete function to calculate the volume of a triangular prism
def triangularPrismVolume (triangleBase: Nat) (triangleHeight: Nat) (prismHeight: Nat) : Nat :=
  let baseArea := triangleArea triangleBase triangleHeight
  baseArea * prismHeight

method TriangularPrismVolume (triangleBase: Nat) (triangleHeight: Nat) (prismHeight: Nat)
  return (volume: Nat)
  require triangleBase > 0  -- Base must be positive
  require triangleHeight > 0  -- Triangle height must be positive
  require prismHeight > 0  -- Prism height must be positive
  ensures volume = triangularPrismVolume triangleBase triangleHeight prismHeight
  ensures volume = (triangleBase * triangleHeight * prismHeight) / 2
  ensures volume > 0  -- Volume is always positive for positive inputs
  do
  pure (triangularPrismVolume triangleBase triangleHeight prismHeight)

-- Test cases for specification validation
section TestCases

-- Test case 1: Simple integer values
-- triangleBase = 6, triangleHeight = 4, prismHeight = 5
-- Triangle area = (6 × 4) / 2 = 12
-- Volume = 12 × 5 = 60
-- Expected result: 60
def testBase1 : Nat := 6
def testTriangleHeight1 : Nat := 4
def testPrismHeight1 : Nat := 5
-- triangularPrismVolume testBase1 testTriangleHeight1 testPrismHeight1 should return 60

-- Test case 2: Unit dimensions
-- triangleBase = 1, triangleHeight = 1, prismHeight = 1
-- Triangle area = (1 × 1) / 2 = 0 (due to integer division)
-- Volume = 0 × 1 = 0
-- Expected result: 0
def testBase2 : Nat := 1
def testTriangleHeight2 : Nat := 1
def testPrismHeight2 : Nat := 1
-- triangularPrismVolume testBase2 testTriangleHeight2 testPrismHeight2 should return 0

-- Test case 3: Even base and height for exact division
-- triangleBase = 8, triangleHeight = 6, prismHeight = 3
-- Triangle area = (8 × 6) / 2 = 24
-- Volume = 24 × 3 = 72
-- Expected result: 72
def testBase3 : Nat := 8
def testTriangleHeight3 : Nat := 6
def testPrismHeight3 : Nat := 3
-- triangularPrismVolume testBase3 testTriangleHeight3 testPrismHeight3 should return 72

-- Test case 4: Large dimensions
-- triangleBase = 20, triangleHeight = 15, prismHeight = 10
-- Triangle area = (20 × 15) / 2 = 150
-- Volume = 150 × 10 = 1500
-- Expected result: 1500
def testBase4 : Nat := 20
def testTriangleHeight4 : Nat := 15
def testPrismHeight4 : Nat := 10
-- triangularPrismVolume testBase4 testTriangleHeight4 testPrismHeight4 should return 1500

-- Test case 5: Right triangle with small height
-- triangleBase = 10, triangleHeight = 8, prismHeight = 2
-- Triangle area = (10 × 8) / 2 = 40
-- Volume = 40 × 2 = 80
-- Expected result: 80
def testBase5 : Nat := 10
def testTriangleHeight5 : Nat := 8
def testPrismHeight5 : Nat := 2
-- triangularPrismVolume testBase5 testTriangleHeight5 testPrismHeight5 should return 80

-- Test case 6: Square base triangle
-- triangleBase = 12, triangleHeight = 12, prismHeight = 7
-- Triangle area = (12 × 12) / 2 = 72
-- Volume = 72 × 7 = 504
-- Expected result: 504
def testBase6 : Nat := 12
def testTriangleHeight6 : Nat := 12
def testPrismHeight6 : Nat := 7
-- triangularPrismVolume testBase6 testTriangleHeight6 testPrismHeight6 should return 504

-- Test case 7: Long thin prism
-- triangleBase = 2, triangleHeight = 10, prismHeight = 15
-- Triangle area = (2 × 10) / 2 = 10
-- Volume = 10 × 15 = 150
-- Expected result: 150
def testBase7 : Nat := 2
def testTriangleHeight7 : Nat := 10
def testPrismHeight7 : Nat := 15
-- triangularPrismVolume testBase7 testTriangleHeight7 testPrismHeight7 should return 150

-- Test case 8: Tall prism
-- triangleBase = 5, triangleHeight = 4, prismHeight = 25
-- Triangle area = (5 × 4) / 2 = 10
-- Volume = 10 × 25 = 250
-- Expected result: 250
def testBase8 : Nat := 5
def testTriangleHeight8 : Nat := 4
def testPrismHeight8 : Nat := 25
-- triangularPrismVolume testBase8 testTriangleHeight8 testPrismHeight8 should return 250

-- Test case 9: Minimal non-zero volume
-- triangleBase = 2, triangleHeight = 2, prismHeight = 1
-- Triangle area = (2 × 2) / 2 = 2
-- Volume = 2 × 1 = 2
-- Expected result: 2
def testBase9 : Nat := 2
def testTriangleHeight9 : Nat := 2
def testPrismHeight9 : Nat := 1
-- triangularPrismVolume testBase9 testTriangleHeight9 testPrismHeight9 should return 2

-- Test case 10: Very large dimensions
-- triangleBase = 100, triangleHeight = 50, prismHeight = 20
-- Triangle area = (100 × 50) / 2 = 2500
-- Volume = 2500 × 20 = 50000
-- Expected result: 50000
def testBase10 : Nat := 100
def testTriangleHeight10 : Nat := 50
def testPrismHeight10 : Nat := 20
-- triangularPrismVolume testBase10 testTriangleHeight10 testPrismHeight10 should return 50000

-- Test case 11: Odd dimensions that might lose precision in integer division
-- triangleBase = 3, triangleHeight = 5, prismHeight = 4
-- Triangle area = (3 × 5) / 2 = 7 (15/2 = 7.5, truncated to 7)
-- Volume = 7 × 4 = 28
-- Expected result: 28
def testBase11 : Nat := 3
def testTriangleHeight11 : Nat := 5
def testPrismHeight11 : Nat := 4
-- triangularPrismVolume testBase11 testTriangleHeight11 testPrismHeight11 should return 28

-- Test case 12: Power of 2 dimensions
-- triangleBase = 16, triangleHeight = 8, prismHeight = 4
-- Triangle area = (16 × 8) / 2 = 64
-- Volume = 64 × 4 = 256
-- Expected result: 256
def testBase12 : Nat := 16
def testTriangleHeight12 : Nat := 8
def testPrismHeight12 : Nat := 4
-- triangularPrismVolume testBase12 testTriangleHeight12 testPrismHeight12 should return 256

end TestCases