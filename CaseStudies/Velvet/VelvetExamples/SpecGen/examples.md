### Examples

Here are some examples to guide you write better specifications and reviews

#### Example1

-- MBPP Problem 3: Write a Velvet function to identify non-prime numbers
--
-- Natural language breakdown:
-- 1. We need to identify non-prime numbers (numbers that are NOT prime)
-- 2. A prime number is a natural number greater than 1 that has exactly two positive divisors: 1 and itself
-- 3. By mathematical convention, 1 is neither prime nor composite, but is considered non-prime
-- 4. Non-prime numbers are: 1 and all composite numbers (numbers with more than 2 positive divisors)
-- 5. Examples of non-prime numbers: 1, 4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, ...
-- 6. Examples of prime numbers: 2, 3, 5, 7, 11, 13, 17, 19, 23, ...
-- 7. The function should return true if the input is non-prime, false if it's prime
-- 8. Edge case: 0 is typically considered non-prime (neither prime nor composite)

Review: This breakdown is very clear and well-structured. The natural language description is precise and detailed, accurately defining non-prime numbers. Edge cases, such as 0 and 1, are explicitly considered.

-- Helper definition to count divisors of a natural number
def countDivisors (n: Nat) : Nat :=
  (List.range (n + 1)).filter (fun d => d > 0 ∧ n % d = 0) |>.length

-- Helper definition for prime numbers
def isPrime (n: Nat) : Prop :=
  n > 1 ∧ countDivisors n = 2

-- Helper definition for composite numbers
def isComposite (n: Nat) : Prop :=
  n > 1 ∧ countDivisors n > 2

method IsNonPrime (n: Nat)
  return (result: Bool)
  ensures result ↔ ¬isPrime n
  do
  pure true  -- placeholder body for type checking

-- Test cases for specification validation
section TestCases

-- Test case 1: Small non-prime numbers (including edge cases)
-- Input: 0 → Expected: true (0 is non-prime)
-- Input: 1 → Expected: true (1 is non-prime by convention)
-- Input: 4 → Expected: true (4 = 2×2, composite, hence non-prime)

-- Test case 2: Small prime numbers
-- Input: 2 → Expected: false (2 is prime)
-- Input: 3 → Expected: false (3 is prime)
-- Input: 5 → Expected: false (5 is prime)
-- Input: 7 → Expected: false (7 is prime)

-- Test case 3: Larger non-prime numbers (composite)
-- Input: 8 → Expected: true (8 = 2×4, composite, hence non-prime)
-- Input: 9 → Expected: true (9 = 3×3, composite, hence non-prime)
-- Input: 10 → Expected: true (10 = 2×5, composite, hence non-prime)
-- Input: 12 → Expected: true (12 = 3×4, composite, hence non-prime)
-- Input: 15 → Expected: true (15 = 3×5, composite, hence non-prime)

-- Test case 4: Larger prime numbers
-- Input: 11 → Expected: false (11 is prime)
-- Input: 13 → Expected: false (13 is prime)
-- Input: 17 → Expected: false (17 is prime)
-- Input: 19 → Expected: false (19 is prime)

-- Test case 5: Perfect squares (all non-prime except for primes squared)
-- Input: 16 → Expected: true (16 = 4×4, composite, hence non-prime)
-- Input: 25 → Expected: true (25 = 5×5, composite, hence non-prime)

-- Verification that our specification captures the correct behavior:
-- 1. Returns true for 0 and 1 (edge cases, non-prime by convention)
-- 2. Returns true for composite numbers (more than 2 divisors)
-- 3. Returns false for prime numbers (exactly 2 divisors: 1 and itself)
-- 4. Handles the smallest prime (2) correctly
-- 5. Works for both small and larger numbers

Review: 

**Definition Accuracy**: 10/10. The specification precisely defines non-prime numbers, clearly distinguishing them from prime numbers and including edge cases such as 0 and 1. 
**Completeness**: 10/10. All essential inputs, outputs, preconditions, and postconditions are specified. No important constraints are missed.
**Conciseness**: 9/10. Definition of isComposite is not used. But overall the definition is concise.
**Testcases:** 10/10. The proposed test cases are well-chosen. They effectively validate both prime and non-prime scenarios.

#### Example2

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

Review:

Overall, the specification is correct and clearly describes the problem. However, it could be further refined by explicitly defining how a path is represented—for example, as a `List (Nat × Nat)` where each consecutive element increases either the row or column by 1. This would make the specification more precise and fully formalizable.

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
  require m < cost.size
  require n < cost[0]!.size
  ensures ∃ path, isValidPath path 0 0 m n ∧ pathCost cost path = minCost  -- achievable minimum
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

Review: 

**Definition Accuracy**: 9/10. The specification defines paths, path validity, and path cost clearly, capturing the essential logic of the minimum-cost path problem. However, the representation of a path could be slightly more explicit (e.g., clarifying that consecutive elements increase either the row or column by 1) to fully formalize the movement constraints.

**Completeness**: 5/10. It misses an important precondition: the input matrix should be rectangular, meaning that for all i, `path[i]!` should have the same size. Additionally, it only states that there exists a path whose cost equals the return value, but does not specify that the cost of every valid path is greater than or equal to the return value.

**Conciseness**: 9/10. The specification is mostly concise and readable. The edge condition in the postcondition is unnecessary, as it can be derived from the common case specified earlier.

**Testcases**: 10/10. The provided test cases cover typical, edge, and moderately complex scenarios, effectively validating that the specification behaves as intended across different inputs.

#### Example3

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

Review:
The specification is clear and well-structured. It accurately defines what constitutes a word and correctly captures the requirements for extracting words of length ≥ 4, preserving order and multiplicity. Edge cases, such as no qualifying words, are explicitly addressed. Overall, the specification demonstrates high semantic accuracy and completeness.

-- Helper function to check if a character is alphabetic (letter)
-- In a real implementation, this would use proper Unicode character classification
def isLetter (c : Char) : Prop := c.isAlpha

-- Helper function to determine if a string is a valid word (all alphabetic characters)
def isWord (s : String) : Prop := s.length > 0 ∧ ∀ c ∈ s.data, isLetter c

-- Axiomatic function to extract all words from a string
-- This conceptually represents what regex word extraction would do
-- Properties:
-- 1. All returned strings are valid words (sequences of alphabetic characters)
-- 2. Words appear in the same order as in the input string
-- 3. Each word appears as many times as it occurs in the input
-- 4. Empty input returns empty list
-- 5. If input contains only non-alphabetic characters, returns empty list
axiom extractWords (input : String) : List String

-- Axioms defining the behavior of extractWords
axiom extractWords_all_valid : ∀ input word, word ∈ extractWords input → isWord word
axiom extractWords_empty : extractWords "" = []
axiom extractWords_complete : ∀ input, (∀ c ∈ input.data, ¬isLetter c) → extractWords input = []

method FindLongWords (input : String)
  return (result: List String)
  ensures ∀ word ∈ result, isWord word ∧ word.length ≥ 4  -- all results are valid words >= 4 chars
  ensures ∀ word ∈ extractWords input, word.length ≥ 4 → word ∈ result  -- all qualifying words included
  ensures ∀ word ∈ result, word ∈ extractWords input  -- only words from input included
  ensures input = "" → result = []  -- empty input gives empty result
  ensures (∀ word ∈ extractWords input, word.length < 4) → result = []  -- no long words = empty result
  do
  pure []  -- placeholder body for type checking

-- Test case 1: Basic string with mixed length words
-- input = "The quick brown fox jumps over lazy dog"
-- words: ["The", "quick", "brown", "fox", "jumps", "over", "lazy", "dog"]
-- words >= 4 chars: ["quick", "brown", "jumps", "over", "lazy"]
-- Expected result: ["quick", "brown", "jumps", "over", "lazy"]
def testInput1 : String := "The quick brown fox jumps over lazy dog"

-- Test case 2: String with punctuation and numbers
-- input = "Hello, world! This is a test123 string."
-- words: ["Hello", "world", "This", "is", "a", "test", "string"]
-- words >= 4 chars: ["Hello", "world", "This", "test", "string"]
-- Expected result: ["Hello", "string"]
def testInput2 : String := "Hello, world! This is a test123 string."

-- Test case 3: No words >= 4 characters
-- input = "A big cat ate pie"
-- words: ["A", "big", "cat", "ate", "pie"]
-- words >= 4 chars: none
-- Expected result: []
def testInput3 : String := "A big cat ate pie"  

Review:
**Definition Accuracy**: 2/10. While the specification passes Lean type checking, key concepts such as word extraction are represented axiomatically via `extractWords`. This means that the mathematical definition of word extraction is not fully formalized within Lean, and the specification relies on assumed properties rather than concrete definitions.

**Completeness**: 8/10. The overall logic of the specification is correct and captures all the main requirements of the problem: (1) all returned words have length ≥ 4, and (2) all words of length ≥ 4 in the input are included in the result. However, since the specification relies on the axiomatic `extractWords` without fully defining how words are extracted, some details of the behavior are left unspecified, which reduces the completeness score.

**Conciseness**: 8/10. The specification is mostly concise and readable. The edge condition in the postcondition is unnecessary, as it can be derived from the common case specified earlier.

**Testcases**: 4/10. The provided test cases are insufficient and contain errors—for example, the expected result for Test Case 2 is incorrect, listing only ["Hello", "string"] instead of all words with length ≥ 4. Furthermore, many important edge cases are missing, such as empty strings, strings with only non-alphabetic characters. The current set of test cases does not adequately validate the specification.