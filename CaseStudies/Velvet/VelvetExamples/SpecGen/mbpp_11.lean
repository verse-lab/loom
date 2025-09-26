import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

-- MBPP Problem 11: Remove first and last occurrence of a given character from the string
--
-- Natural language breakdown:
-- 1. Given a string and a target character, we need to remove exactly two occurrences
-- 2. Remove the first occurrence of the character (leftmost position)
-- 3. Remove the last occurrence of the character (rightmost position)
-- 4. If the character appears only once, remove just that single occurrence
-- 5. If the character doesn't appear at all, return the original string unchanged
-- 6. If the character appears multiple times, only remove the first and last occurrences
-- 7. Characters between first and last occurrences should remain untouched
-- 8. The relative order of all other characters should be preserved

-- Helper function to find the first occurrence index of a character in a string
def findFirstIndex (s: String) (c: Char) : Option Nat :=
  s.toList.findIdx? (· == c)

-- Helper function to find the last occurrence index of a character in a string
def findLastIndex (s: String) (c: Char) : Option Nat :=
  let chars := s.toList
  let reversed_chars := chars.reverse
  match reversed_chars.findIdx? (· == c) with
  | none => none
  | some rev_idx => some (chars.length - 1 - rev_idx)

-- Helper function to remove character at a specific index from a string
def removeCharAt (s: String) (idx: Nat) : String :=
  let chars := s.toList
  if idx < chars.length then
    String.mk (chars.take idx ++ chars.drop (idx + 1))
  else s

-- Concrete function to remove first and last occurrences of a character
def removeFirstAndLast (s: String) (c: Char) : String :=
  match findFirstIndex s c, findLastIndex s c with
  | none, _ => s  -- Character not found, return original string
  | some first_idx, none => s  -- This case shouldn't happen, but handle it
  | some first_idx, some last_idx =>
    if first_idx == last_idx then
      -- Only one occurrence, remove it
      removeCharAt s first_idx
    else
      -- Multiple occurrences, remove both first and last
      -- Remove last first to avoid index shifting issues
      let after_last_removed := removeCharAt s last_idx
      removeCharAt after_last_removed first_idx

method RemoveFirstAndLastChar (s: String) (c: Char)
  return (result: String)
  ensures result = removeFirstAndLast s c
  ensures (findFirstIndex s c).isNone → result = s  -- If character not found, string unchanged
  ensures (findFirstIndex s c).isSome → result.length ≤ s.length  -- Result is never longer
  do
  pure (removeFirstAndLast s c)

-- Test cases for specification validation
section TestCases

-- Test case 1: Character appears multiple times
-- s = "hello world", c = 'l'
-- First 'l' at index 2, last 'l' at index 9
-- Expected result: "helo word" (remove 'l' at positions 2 and 9)
def testString1 : String := "hello world"
def testChar1 : Char := 'l'
-- removeFirstAndLast testString1 testChar1 should return "helo word"

-- Test case 2: Character appears only once
-- s = "hello", c = 'h'
-- Only 'h' at index 0
-- Expected result: "ello" (remove single occurrence)
def testString2 : String := "hello"
def testChar2 : Char := 'h'
-- removeFirstAndLast testString2 testChar2 should return "ello"

-- Test case 3: Character doesn't appear
-- s = "hello", c = 'x'
-- No 'x' found
-- Expected result: "hello" (unchanged)
def testString3 : String := "hello"
def testChar3 : Char := 'x'
-- removeFirstAndLast testString3 testChar3 should return "hello"

-- Test case 4: All characters are the same
-- s = "aaaa", c = 'a'
-- First 'a' at index 0, last 'a' at index 3
-- Expected result: "aa" (remove first and last 'a')
def testString4 : String := "aaaa"
def testChar4 : Char := 'a'
-- removeFirstAndLast testString4 testChar4 should return "aa"

-- Test case 5: Two adjacent occurrences
-- s = "abba", c = 'b'
-- First 'b' at index 1, last 'b' at index 2
-- Expected result: "aa" (remove both 'b' characters)
def testString5 : String := "abba"
def testChar5 : Char := 'b'
-- removeFirstAndLast testString5 testChar5 should return "aa"

-- Test case 6: Character at start and end
-- s = "abcda", c = 'a'
-- First 'a' at index 0, last 'a' at index 4
-- Expected result: "bcd" (remove 'a' from both ends)
def testString6 : String := "abcda"
def testChar6 : Char := 'a'
-- removeFirstAndLast testString6 testChar6 should return "bcd"

-- Test case 7: Empty string
-- s = "", c = 'a'
-- No characters to remove
-- Expected result: "" (unchanged)
def testString7 : String := ""
def testChar7 : Char := 'a'
-- removeFirstAndLast testString7 testChar7 should return ""

-- Test case 8: Single character string - matches target
-- s = "a", c = 'a'
-- Only one 'a' at index 0 (first and last are the same)
-- Expected result: "" (remove the single character)
def testString8 : String := "a"
def testChar8 : Char := 'a'
-- removeFirstAndLast testString8 testChar8 should return ""

-- Test case 9: Single character string - doesn't match target
-- s = "a", c = 'b'
-- No 'b' found
-- Expected result: "a" (unchanged)
def testString9 : String := "a"
def testChar9 : Char := 'b'
-- removeFirstAndLast testString9 testChar9 should return "a"

-- Test case 10: Many occurrences in between
-- s = "abbbbbba", c = 'b'
-- First 'b' at index 1, last 'b' at index 6
-- Expected result: "abbbba" (remove first and last 'b', keep middle ones)
def testString10 : String := "abbbbbba"
def testChar10 : Char := 'b'
-- removeFirstAndLast testString10 testChar10 should return "abbbba"

-- Test case 11: First and last are same (palindrome case)
-- s = "racecar", c = 'r'
-- First 'r' at index 0, last 'r' at index 6
-- Expected result: "aceca" (remove 'r' from both ends)
def testString11 : String := "racecar"
def testChar11 : Char := 'r'
-- removeFirstAndLast testString11 testChar11 should return "aceca"

-- Test case 12: Complex case with multiple different characters
-- s = "programming", c = 'm'
-- First 'm' at index 5, last 'm' at index 10
-- Expected result: "prograin" (remove 'm' at positions 5 and 10)
def testString12 : String := "programming"
def testChar12 : Char := 'm'
-- removeFirstAndLast testString12 testChar12 should return "prograin"

end TestCases