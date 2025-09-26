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

-- Longest Common Substring Problem
--
-- Natural language breakdown:
-- 1. We have two input strings (s1 and s2)
-- 2. A substring of a string is any contiguous sequence of characters from that string
-- 3. A common substring is a substring that appears in both input strings
-- 4. The longest common substring is a common substring with maximum length
-- 5. If multiple common substrings exist with the same maximum length, any one of them is valid
-- 6. If no common substring exists, the result should be an empty string
-- 7. The result must be a valid substring of both input strings
-- 8. No longer common substring should exist

-- Helper definition to check if a string is a substring of another string
def isSubstring (sub: String) (str: String) : Prop :=
  ∃ start : Nat, start + sub.length ≤ str.length ∧
  str.extract ⟨start⟩ ⟨start + sub.length⟩ = sub

-- Helper definition to check if a string is a common substring of two strings
def isCommonSubstring (sub: String) (s1 s2: String) : Prop :=
  isSubstring sub s1 ∧ isSubstring sub s2

-- Helper definition to get all possible substrings of a string
def getAllSubstrings (s: String) : List String :=
  let chars := s.toList
  (List.range s.length).flatMap fun i =>
    (List.range (s.length - i + 1)).filterMap fun len =>
      if len = 0 then none
      else some (String.mk (chars.drop i |>.take len))

method LongestCommonSubstring (s1: String) (s2: String)
  return (result: String)
  ensures isCommonSubstring result s1 s2  -- result is a common substring
  ensures ∀ sub, isCommonSubstring sub s1 s2 → sub.length ≤ result.length  -- result is longest
  ensures (s1 = "" ∨ s2 = "") → result = ""  -- empty strings case
  ensures s1 = s2 → result = s1  -- identical strings case
  ensures (result = "") ↔ (∀ sub, sub ≠ "" → ¬isCommonSubstring sub s1 s2)  -- empty result iff no non-empty common substring exists
  ensures (∃ sub, sub ≠ "" ∧ isCommonSubstring sub s1 s2) → result ≠ ""  -- non-empty result when common substrings exist
  do
  pure ""  -- placeholder body for type checking

-- Test cases for specification validation
section TestCases

-- Test case 1: Basic common substring
-- s1 = "ABABC", s2 = "BABCA"
-- Expected: "BABC" (length 4)
-- Common substrings include: "A", "B", "AB", "BA", "ABC", "BABC"
def testS1_1 : String := "ABABC"
def testS2_1 : String := "BABCA"

-- Test case 2: No common substring
-- s1 = "ABC", s2 = "DEF"
-- Expected: "" (empty string)
def testS1_2 : String := "ABC"
def testS2_2 : String := "DEF"

-- Test case 3: One empty string
-- s1 = "HELLO", s2 = ""
-- Expected: "" (empty string)
def testS1_3 : String := "HELLO"
def testS2_3 : String := ""

-- Test case 4: Identical strings
-- s1 = "SAME", s2 = "SAME"
-- Expected: "SAME" (the entire string)
def testS1_4 : String := "SAME"
def testS2_4 : String := "SAME"

-- Test case 5: Overlapping patterns
-- s1 = "GeeksforGeeks", s2 = "GeeksQuiz"
-- Expected: "Geeks" (length 5)
def testS1_5 : String := "GeeksforGeeks"
def testS2_5 : String := "GeeksQuiz"

-- Test case 6: Single character common
-- s1 = "XYZ", s2 = "ABC"
-- Expected: "" (no common characters)
def testS1_6 : String := "XYZ"
def testS2_6 : String := "ABC"

-- Test case 7: Multiple substrings of same length
-- s1 = "ABCDXYZ", s2 = "XYZABCD"
-- Expected: Either "ABCD" or "XYZ" (both have length 3, but "ABCD" has length 4)
-- Actually "ABCD" is longer (length 4) than "XYZ" (length 3)
def testS1_7 : String := "ABCDXYZ"
def testS2_7 : String := "XYZABCD"

-- Test case 8: Repeated characters
-- s1 = "AAAA", s2 = "AAA"
-- Expected: "AAA" (length 3)
def testS1_8 : String := "AAAA"
def testS2_8 : String := "AAA"

-- Note: The test cases demonstrate the specification's intended behavior:
-- 1. Finding longest common substring in typical cases
-- 2. Handling empty results when no common substring exists
-- 3. Proper handling of empty input strings
-- 4. Correct behavior when strings are identical
-- 5. Complex cases with multiple potential substrings
-- 6. Edge cases with no common characters
-- 7. Cases with multiple longest substrings of same length
-- 8. Handling of repeated character patterns

end TestCases