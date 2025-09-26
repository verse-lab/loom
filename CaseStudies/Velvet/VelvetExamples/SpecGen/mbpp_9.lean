import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

-- MBPP Problem 9: Find the minimum number of rotations required to get the same string
--
-- Natural language breakdown:
-- 1. Given a string s, we want to find the minimum number of rotations needed
--    to make the string equal to itself (i.e., find its period)
-- 2. A rotation of a string moves characters from the front to the back
--    For example, rotating "abc" once gives "bca", rotating twice gives "cab"
-- 3. The minimum number of rotations is the length of the shortest repeating pattern
--    For "abcabc", the pattern "abc" repeats, so minimum rotations = 3
-- 4. For a string of length n, the answer is always between 1 and n
-- 5. If no proper rotation works, then the minimum rotations equals the string length
-- 6. Special case: empty string should return 0 rotations

-- Helper function to rotate a string k positions to the left
def rotateString (s: String) (k: Nat) : String :=
  if s.length = 0 then s
  else
    let k_mod := k % s.length
    let chars := s.toList
    let rotated := chars.drop k_mod ++ chars.take k_mod
    String.mk rotated

-- Helper function to check if k rotations produce the original string
def isValidRotation (s: String) (k: Nat) : Bool :=
  rotateString s k = s

-- Concrete function to find minimum rotations
def findMinRotations (s: String) : Nat :=
  if s.length = 0 then 0
  else
    let rec findMin (k: Nat) : Nat :=
      if k > s.length then s.length
      else if isValidRotation s k then k
      else findMin (k + 1)
    termination_by s.length + 1 - k
    findMin 1

method MinRotations (s: String)
  return (minRot: Nat)
  ensures s.length = 0 → minRot = 0  -- empty string case
  ensures s.length > 0 → minRot > 0 ∧ minRot ≤ s.length  -- bounds for non-empty strings
  ensures minRot = findMinRotations s  -- result matches the concrete function
  do
  pure (findMinRotations s)

-- Test cases for specification validation
section TestCases

-- Test case 1: String with clear repeating pattern
-- s = "abcabc"
-- Pattern "abc" repeats, so minimum rotations = 3
-- Rotating 3 positions: "abcabc" → "abcabc" ✓
def testString1 : String := "abcabc"

-- Test case 2: String with single character repeated
-- s = "aaaa"
-- Pattern "a" repeats, so minimum rotations = 1
-- Rotating 1 position: "aaaa" → "aaaa" ✓
def testString2 : String := "aaaa"

-- Test case 3: No proper repeating pattern
-- s = "abcd"
-- No proper period exists, so minimum rotations = 4 (full string length)
-- Only rotating 4 positions gives back the original: "abcd" → "abcd" ✓
def testString3 : String := "abcd"

-- Test case 4: Two-character pattern
-- s = "abab"
-- Pattern "ab" repeats, so minimum rotations = 2
-- Rotating 2 positions: "abab" → "abab" ✓
def testString4 : String := "abab"

-- Test case 5: Single character string
-- s = "x"
-- Only one character, so minimum rotations = 1
-- Rotating 1 position: "x" → "x" ✓
def testString5 : String := "x"

-- Test case 6: Empty string (edge case)
-- s = ""
-- Empty string should return 0 rotations by definition
def testString6 : String := ""

-- Test case 7: Complex pattern
-- s = "abcabcabc"
-- Pattern "abc" repeats 3 times, so minimum rotations = 3
-- Rotating 3 positions: "abcabcabc" → "abcabcabc" ✓
def testString7 : String := "abcabcabc"

-- Note: The test cases demonstrate different scenarios:
-- 1. Clear repeating patterns of various lengths
-- 2. Single character repetition (degenerate case)
-- 3. No proper period (result equals string length)
-- 4. Multiple character patterns
-- 5. Minimal input (single character)
-- 6. Edge case (empty string)
-- 7. Longer patterns with multiple repetitions

end TestCases
