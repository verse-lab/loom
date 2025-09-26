import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

-- MBPP Problem 7: Find all words which are at least 4 characters long in a string by using regex
--
-- Natural language breakdown:
-- 1. We have an input string that contains words separated by whitespace and possibly punctuation
-- 2. A "word" is defined as a contiguous sequence of alphabetic characters (letters)
-- 3. We want to extract all words from the string that have length >= 4
-- 4. The function should return a list of these words
-- 5. Words should appear in the result in the same order they appear in the input string
-- 6. Each qualifying word should appear in the result as many times as it appears in the input
-- 7. If no words of length >= 4 exist, return an empty list
-- 8. Non-alphabetic characters (digits, punctuation, whitespace) serve as word separators

-- Helper function to check if a character is alphabetic (letter)
def isLetter (c : Char) : Bool := c.isAlpha

-- Helper function to determine if a string is a valid word (all alphabetic characters)
def isWord (s : String) : Bool := s.length > 0 && s.data.all isLetter

-- Concrete function to split string by non-alphabetic characters and extract words
def extractWords (input : String) : List String :=
  -- Split the string by non-alphabetic characters
  let chars := input.data
  let rec splitByNonAlpha (chars : List Char) (current : List Char) (acc : List String) : List String :=
    match chars with
    | [] =>
        if current.isEmpty then acc.reverse
        else (String.mk current.reverse :: acc).reverse
    | c :: rest =>
        if isLetter c then
          splitByNonAlpha rest (c :: current) acc
        else
          if current.isEmpty then
            splitByNonAlpha rest [] acc
          else
            splitByNonAlpha rest [] (String.mk current.reverse :: acc)
  splitByNonAlpha chars [] []


method FindLongWords (input : String)
  return (result: List String)
  ensures ∀ word ∈ result, word.length ≥ 4  -- all results are >= 4 chars
  ensures result = (extractWords input).filter (fun word => word.length ≥ 4)  -- result is exactly the filtered words
  do
  pure ((extractWords input).filter (fun word => word.length ≥ 4))

-- Test cases for specification validation
section TestCases

-- Test case 1: Basic string with mixed length words
-- Input: "The quick brown fox jumps over lazy dog"
-- Expected words extracted: ["The", "quick", "brown", "fox", "jumps", "over", "lazy", "dog"]
-- Expected words >= 4 chars: ["quick", "brown", "jumps", "over", "lazy"]
def testInput1 : String := "The quick brown fox jumps over lazy dog"

-- Test case 2: String with punctuation and numbers as separators
-- Input: "Hello, world! This is a test123 string."
-- Expected words extracted: ["Hello", "world", "This", "is", "a", "test", "string"]
-- Expected words >= 4 chars: ["Hello", "world", "This", "test", "string"]
def testInput2 : String := "Hello, world! This is a test123 string."

-- Test case 3: No words >= 4 characters (all short words)
-- Input: "A big cat ate pie"
-- Expected words extracted: ["A", "big", "cat", "ate", "pie"]
-- Expected words >= 4 chars: [] (empty list)
def testInput3 : String := "A big cat ate pie"

-- Test case 4: Empty string (edge case)
-- Input: ""
-- Expected words extracted: []
-- Expected words >= 4 chars: []
def testInput4 : String := ""

-- Test case 5: Only non-alphabetic characters
-- Input: "   !!!  @@@ ### $$$   "
-- Expected words extracted: [] (no alphabetic characters)
-- Expected words >= 4 chars: []
def testInput5 : String := "   !!!  @@@ ### $$$   "

-- Test case 6: Repeated words (multiplicity preservation)
-- Input: "programming programming code code development"
-- Expected words extracted: ["programming", "programming", "code", "code", "development"]
-- Expected words >= 4 chars: ["programming", "programming", "code", "code", "development"]
def testInput6 : String := "programming programming code code development"

-- Test case 7: Boundary case - words exactly 4 characters
-- Input: "test code work play"
-- Expected words extracted: ["test", "code", "work", "play"]
-- Expected words >= 4 chars: ["test", "code", "work", "play"] (all exactly 4 chars)
def testInput7 : String := "test code work play"

-- Test case 8: Very long words mixed with short words
-- Input: "supercalifragilisticexpialidocious a extraordinarily long word"
-- Expected words extracted: ["supercalifragilisticexpialidocious", "a", "extraordinarily", "long", "word"]
-- Expected words >= 4 chars: ["supercalifragilisticexpialidocious", "extraordinarily", "long", "word"]
def testInput8 : String := "supercalifragilisticexpialidocious a extraordinarily long word"

-- Test case 9: Mixed case letters (all alphabetic characters should be preserved)
-- Input: "Programming LANGUAGE design"
-- Expected words extracted: ["Programming", "LANGUAGE", "design"]
-- Expected words >= 4 chars: ["Programming", "LANGUAGE", "design"]
def testInput9 : String := "Programming LANGUAGE design"

-- Test case 10: Words separated by multiple types of separators
-- Input: "one123two@@@three   four!!!five"
-- Expected words extracted: ["one", "two", "three", "four", "five"]
-- Expected words >= 4 chars: ["three", "four", "five"]
def testInput10 : String := "one123two@@@three   four!!!five"

-- Additional edge case: Words at boundaries
-- Input: "word start end"
-- Expected words extracted: ["word", "start", "end"]
-- Expected words >= 4 chars: ["word", "start"]
def testInput11 : String := "word start end"

end TestCases
