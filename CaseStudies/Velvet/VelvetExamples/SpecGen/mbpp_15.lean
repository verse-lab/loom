import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

-- MBPP Problem 15: Split a string at lowercase letters
--
-- Natural language breakdown:
-- 1. Given a string, split it into substrings at positions where lowercase letters occur
-- 2. The lowercase letters themselves serve as delimiters and are not included in the result
-- 3. Consecutive lowercase letters create empty strings in the result
-- 4. Leading or trailing lowercase letters create empty strings at the beginning or end
-- 5. If the string contains only lowercase letters, the result should be all empty strings
-- 6. If the string contains no lowercase letters, return the entire string as a single element
-- 7. Uppercase letters, digits, and special characters remain in the result
-- 8. Empty input string returns a list containing one empty string

-- Helper function to check if a character is a lowercase letter
def isLowercase (c: Char) : Bool :=
  c.isAlpha && c.isLower

-- Concrete function to split string at lowercase letters
def splitAtLowercase (s: String) : List String :=
  let chars := s.toList
  let rec splitHelper (remaining: List Char) (current: List Char) (acc: List String) : List String :=
    match remaining with
    | [] =>
      -- End of string, add current accumulated characters
      (String.mk current.reverse :: acc).reverse
    | c :: rest =>
      if isLowercase c then
        -- Found lowercase letter, split here (don't include the lowercase letter)
        let newPart := String.mk current.reverse
        splitHelper rest [] (newPart :: acc)
      else
        -- Not lowercase, continue accumulating
        splitHelper rest (c :: current) acc
  splitHelper chars [] []

method SplitAtLowercase (s: String)
  return (result: List String)
  ensures result = splitAtLowercase s
  ensures result.length > 0  -- Always returns at least one string (even if empty)
  ensures s = "" → result = [""]  -- Empty string gives list with one empty string
  do
  pure (splitAtLowercase s)

-- Test cases for specification validation
section TestCases

-- Test case 1: Mixed case with lowercase delimiters
-- s = "HellowWorld"
-- Split at 'o', 'w': "Hell" + "" + "W" + "" + "rld"
-- Expected result: ["Hell", "", "W", "", "rld"]
def testString1 : String := "HellowWorld"
-- splitAtLowercase testString1 should return ["Hell", "", "W", "", "rld"]

-- Test case 2: String starting with lowercase
-- s = "helloWORLD"
-- Split at 'h', 'e', 'l', 'l', 'o': "" + "" + "" + "" + "" + "WORLD"
-- Expected result: ["", "", "", "", "", "WORLD"]
def testString2 : String := "helloWORLD"
-- splitAtLowercase testString2 should return ["", "", "", "", "", "WORLD"]

-- Test case 3: String ending with lowercase
-- s = "WORLDhello"
-- Split at 'h', 'e', 'l', 'l', 'o': "WORLD" + "" + "" + "" + "" + ""
-- Expected result: ["WORLD", "", "", "", "", ""]
def testString3 : String := "WORLDhello"
-- splitAtLowercase testString3 should return ["WORLD", "", "", "", "", ""]

-- Test case 4: No lowercase letters
-- s = "HELLO123!@#"
-- No splits needed
-- Expected result: ["HELLO123!@#"]
def testString4 : String := "HELLO123!@#"
-- splitAtLowercase testString4 should return ["HELLO123!@#"]

-- Test case 5: Only lowercase letters
-- s = "hello"
-- Split at 'h', 'e', 'l', 'l', 'o': "" + "" + "" + "" + "" + ""
-- Expected result: ["", "", "", "", "", ""]
def testString5 : String := "hello"
-- splitAtLowercase testString5 should return ["", "", "", "", "", ""]

-- Test case 6: Empty string
-- s = ""
-- Expected result: [""]
def testString6 : String := ""
-- splitAtLowercase testString6 should return [""]

-- Test case 7: Single lowercase character
-- s = "a"
-- Split at 'a': "" + ""
-- Expected result: ["", ""]
def testString7 : String := "a"
-- splitAtLowercase testString7 should return ["", ""]

-- Test case 8: Single uppercase character
-- s = "A"
-- No splits
-- Expected result: ["A"]
def testString8 : String := "A"
-- splitAtLowercase testString8 should return ["A"]

-- Test case 9: Mixed with digits and symbols
-- s = "A1b2C3d4E"
-- Split at 'b', 'd': "A1" + "2C3" + "4E"
-- Expected result: ["A1", "2C3", "4E"]
def testString9 : String := "A1b2C3d4E"
-- splitAtLowercase testString9 should return ["A1", "2C3", "4E"]

-- Test case 10: Consecutive lowercase letters
-- s = "AabcD"
-- Split at 'a', 'b', 'c': "A" + "" + "" + "D"
-- Expected result: ["A", "", "", "D"]
def testString10 : String := "AabcD"
-- splitAtLowercase testString10 should return ["A", "", "", "D"]

-- Test case 11: Alternating case pattern
-- s = "AbCdEfG"
-- Split at 'b', 'd', 'f': "A" + "C" + "E" + "G"
-- Expected result: ["A", "C", "E", "G"]
def testString11 : String := "AbCdEfG"
-- splitAtLowercase testString11 should return ["A", "C", "E", "G"]

-- Test case 12: Complex string with multiple character types
-- s = "Hello123world456TEST"
-- Split at 'e', 'l', 'l', 'o', 'w', 'o', 'r', 'l', 'd': "H" + "" + "" + "" + "123" + "" + "" + "" + "" + "456TEST"
-- Expected result: ["H", "", "", "", "123", "", "", "", "", "456TEST"]
def testString12 : String := "Hello123world456TEST"
-- splitAtLowercase testString12 should return ["H", "", "", "", "123", "", "", "", "", "456TEST"]

-- Test case 13: String with spaces and lowercase
-- s = "A b C"
-- Split at 'b': "A " + " C"
-- Expected result: ["A ", " C"]
def testString13 : String := "A b C"
-- splitAtLowercase testString13 should return ["A ", " C"]

-- Test case 14: Numbers and lowercase
-- s = "123a456b789"
-- Split at 'a', 'b': "123" + "456" + "789"
-- Expected result: ["123", "456", "789"]
def testString14 : String := "123a456b789"
-- splitAtLowercase testString14 should return ["123", "456", "789"]

-- Test case 15: Only one lowercase in middle
-- s = "HELLOaWORLD"
-- Split at 'a': "HELLO" + "WORLD"
-- Expected result: ["HELLO", "WORLD"]
def testString15 : String := "HELLOaWORLD"
-- splitAtLowercase testString15 should return ["HELLO", "WORLD"]

end TestCases