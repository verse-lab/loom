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

-- MBPP Problem 6: Check whether two numbers differ at one bit position only
--
-- Natural language breakdown:
-- 1. We have two natural numbers (a and b)
-- 2. Two numbers "differ at one bit position only" means exactly one bit differs between them
-- 3. This is equivalent to checking if their XOR (bitwise exclusive OR) has exactly one bit set
-- 4. A number has exactly one bit set if and only if it's a power of 2 (and non-zero)
-- 5. The function should return true if exactly one bit differs, false otherwise
-- 6. If the numbers are equal (no bits differ), the function should return false
-- 7. If more than one bit differs, the function should return false

-- Helper definition to check if a natural number is a power of 2
-- A positive number n is a power of 2 if n & (n-1) = 0 and n > 0
def isPowerOfTwo (n : Nat) : Prop :=
  n > 0 ∧ (n &&& (n - 1)) = 0


method DifferOneBit (a : Nat) (b : Nat)
  return (result: Bool)
  ensures result ↔ isPowerOfTwo (a ^^^ b)
  do
  pure false  -- placeholder body for type checking

-- Test cases for specification validation
section TestCases

-- Test case 1: Numbers that differ at exactly one bit position
-- a = 13 (binary: 1101), b = 9 (binary: 1001)
-- XOR = 13 ^^^ 9 = 4 (binary: 0100) - exactly one bit set at position 2
-- Expected result: true
def testA1 : Nat := 13
def testB1 : Nat := 9

-- Test case 2: Numbers that differ at more than one bit position
-- a = 15 (binary: 1111), b = 0 (binary: 0000)
-- XOR = 15 ^^^ 0 = 15 (binary: 1111) - four bits set
-- Expected result: false
def testA2 : Nat := 15
def testB2 : Nat := 0

-- Test case 3: Identical numbers
-- a = 7 (binary: 0111), b = 7 (binary: 0111)
-- XOR = 7 ^^^ 7 = 0 (binary: 0000) - no bits set
-- Expected result: false
def testA3 : Nat := 7
def testB3 : Nat := 7

-- Test case 4: Adjacent powers of 2 (differ by exactly one bit)
-- a = 8 (binary: 1000), b = 0 (binary: 0000)
-- XOR = 8 ^^^ 0 = 8 (binary: 1000) - exactly one bit set at position 3
-- Expected result: true
def testA4 : Nat := 8
def testB4 : Nat := 0

-- Test case 5: Numbers differing in the least significant bit
-- a = 4 (binary: 100), b = 5 (binary: 101)
-- XOR = 4 ^^^ 5 = 1 (binary: 001) - exactly one bit set at position 0
-- Expected result: true
def testA5 : Nat := 4
def testB5 : Nat := 5

-- Test case 6: Numbers that differ at two bit positions
-- a = 3 (binary: 011), b = 12 (binary: 1100)
-- XOR = 3 ^^^ 12 = 15 (binary: 1111) - multiple bits set
-- Expected result: false
def testA6 : Nat := 3
def testB6 : Nat := 12

-- Test case 7: Large numbers differing at one bit
-- a = 1024 (binary: 10000000000), b = 0 (binary: 0)
-- XOR = 1024 ^^^ 0 = 1024 - exactly one bit set at position 10
-- Expected result: true
def testA7 : Nat := 1024
def testB7 : Nat := 0

-- Note: The test cases demonstrate the specification's intended behavior:
-- 1. True cases: XOR results in a power of 2 (exactly one bit differs)
-- 2. False cases: XOR results in 0 (identical) or non-power of 2 (multiple bits differ)
-- 3. Edge cases: identical numbers, large numbers, and various bit patterns

end TestCases