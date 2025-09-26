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

end TestCases
