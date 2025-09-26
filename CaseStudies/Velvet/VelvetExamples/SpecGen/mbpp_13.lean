import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

-- MBPP Problem 13: Count the most common words in a dictionary
--
-- Natural language breakdown:
-- 1. Given a list of words (strings), count the frequency of each word
-- 2. Find the maximum frequency among all words
-- 3. Return the count of words that have this maximum frequency
-- 4. For example, if word frequencies are: "cat":3, "dog":2, "bird":3, "fish":1
--    then maximum frequency is 3, and there are 2 words with this frequency
-- 5. Case sensitivity matters: "Cat" and "cat" are different words
-- 6. Empty strings are valid words and should be counted if present
-- 7. If the input list is empty, return 0 (no words, so no common words)
-- 8. All words with the highest frequency are considered "most common"

-- Helper function to count occurrences of each word in the list
def countWordFrequencies (words: List String) : List (String × Nat) :=
  let uniqueWords := words.eraseDups
  uniqueWords.map fun word => (word, words.count word)

-- Helper function to find the maximum frequency
def findMaxFrequency (words: List String) : Nat :=
  if words.isEmpty then 0
  else
    let frequencies := countWordFrequencies words
    let freqValues := frequencies.map (·.2)
    freqValues.foldl max 0

-- Concrete function to count most common words
def countMostCommonWords (words: List String) : Nat :=
  if words.isEmpty then 0
  else
    let maxFreq := findMaxFrequency words
    let frequencies := countWordFrequencies words
    (frequencies.filter fun (_, freq) => freq = maxFreq).length

method CountMostCommonWords (words: List String)
  return (result: Nat)
  ensures result = countMostCommonWords words
  ensures words.isEmpty → result = 0  -- Empty list gives 0
  ensures words.length > 0 → result > 0  -- Non-empty list gives positive result
  ensures result ≤ words.eraseDups.length  -- Can't have more common words than unique words
  do
  pure (countMostCommonWords words)

-- Test cases for specification validation
section TestCases

-- Test case 1: Simple case with clear most common words
-- words = ["cat", "dog", "cat", "bird", "cat", "dog"]
-- Frequencies: "cat": 3, "dog": 2, "bird": 1
-- Maximum frequency: 3, Number of words with max frequency: 1 ("cat")
-- Expected result: 1
def testWords1 : List String := ["cat", "dog", "cat", "bird", "cat", "dog"]
-- countMostCommonWords testWords1 should return 1

-- Test case 2: Multiple words with same maximum frequency
-- words = ["apple", "banana", "apple", "banana", "cherry"]
-- Frequencies: "apple": 2, "banana": 2, "cherry": 1
-- Maximum frequency: 2, Number of words with max frequency: 2 ("apple", "banana")
-- Expected result: 2
def testWords2 : List String := ["apple", "banana", "apple", "banana", "cherry"]
-- countMostCommonWords testWords2 should return 2

-- Test case 3: All words appear exactly once
-- words = ["red", "green", "blue", "yellow"]
-- Frequencies: "red": 1, "green": 1, "blue": 1, "yellow": 1
-- Maximum frequency: 1, Number of words with max frequency: 4 (all words)
-- Expected result: 4
def testWords3 : List String := ["red", "green", "blue", "yellow"]
-- countMostCommonWords testWords3 should return 4

-- Test case 4: Single word repeated multiple times
-- words = ["hello", "hello", "hello", "hello"]
-- Frequencies: "hello": 4
-- Maximum frequency: 4, Number of words with max frequency: 1 ("hello")
-- Expected result: 1
def testWords4 : List String := ["hello", "hello", "hello", "hello"]
-- countMostCommonWords testWords4 should return 1

-- Test case 5: Empty list
-- words = []
-- No words to count
-- Expected result: 0
def testWords5 : List String := []
-- countMostCommonWords testWords5 should return 0

-- Test case 6: Single word
-- words = ["single"]
-- Frequencies: "single": 1
-- Maximum frequency: 1, Number of words with max frequency: 1 ("single")
-- Expected result: 1
def testWords6 : List String := ["single"]
-- countMostCommonWords testWords6 should return 1

-- Test case 7: Case sensitivity test
-- words = ["Cat", "cat", "CAT", "Cat"]
-- Frequencies: "Cat": 2, "cat": 1, "CAT": 1
-- Maximum frequency: 2, Number of words with max frequency: 1 ("Cat")
-- Expected result: 1
def testWords7 : List String := ["Cat", "cat", "CAT", "Cat"]
-- countMostCommonWords testWords7 should return 1

-- Test case 8: Empty strings and special characters
-- words = ["", "test", "", "test", "test", ""]
-- Frequencies: "": 3, "test": 3
-- Maximum frequency: 3, Number of words with max frequency: 2 ("", "test")
-- Expected result: 2
def testWords8 : List String := ["", "test", "", "test", "test", ""]
-- countMostCommonWords testWords8 should return 2

-- Test case 9: Long words with different frequencies
-- words = ["programming", "coding", "programming", "development", "coding", "programming"]
-- Frequencies: "programming": 3, "coding": 2, "development": 1
-- Maximum frequency: 3, Number of words with max frequency: 1 ("programming")
-- Expected result: 1
def testWords9 : List String := ["programming", "coding", "programming", "development", "coding", "programming"]
-- countMostCommonWords testWords9 should return 1

-- Test case 10: Many words with same frequency
-- words = ["a", "b", "c", "a", "b", "c", "d", "d"]
-- Frequencies: "a": 2, "b": 2, "c": 2, "d": 2
-- Maximum frequency: 2, Number of words with max frequency: 4 (all words)
-- Expected result: 4
def testWords10 : List String := ["a", "b", "c", "a", "b", "c", "d", "d"]
-- countMostCommonWords testWords10 should return 4

-- Test case 11: Numbers as strings
-- words = ["1", "2", "1", "3", "2", "1"]
-- Frequencies: "1": 3, "2": 2, "3": 1
-- Maximum frequency: 3, Number of words with max frequency: 1 ("1")
-- Expected result: 1
def testWords11 : List String := ["1", "2", "1", "3", "2", "1"]
-- countMostCommonWords testWords11 should return 1

-- Test case 12: Special characters and spaces
-- words = ["hello world", "test", "hello world", "test", "test"]
-- Frequencies: "hello world": 2, "test": 3
-- Maximum frequency: 3, Number of words with max frequency: 1 ("test")
-- Expected result: 1
def testWords12 : List String := ["hello world", "test", "hello world", "test", "test"]
-- countMostCommonWords testWords12 should return 1

end TestCases