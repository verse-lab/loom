----------------------------------------------------
-- Example 4: Refutations
----------------------------------------------------


-- Spec: Convert a given natural number from decimal to its binary representation.

-- Comment: This example shows even PL PhD students are hard to right a correct
-- invariant at once. Claude missed the last line "invariant num = 0 → result.head?
-- = some 1" at first. So it fails to prove the noLeadingZeros property.
-- Aristotle proves its negation, which contains an counterexample, like this:

import Mathlib.Tactic

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

---------------------------------------------------------
-- The program and the spec
---------------------------------------------------------

-- Helper function: convert a list of binary digits to its decimal value
-- This computes the value by treating the list as big-endian (most significant bit first)
def binaryToDecimal (bits: List Nat) : Nat :=
  bits.foldl (fun acc bit => 2 * acc + bit) 0

-- Helper predicate: all elements in list are valid binary digits (0 or 1)
def allBinaryDigits (bits: List Nat) : Prop :=
  ∀ b ∈ bits, b = 0 ∨ b = 1

-- Helper predicate: check if representation has no leading zeros (except for [0])
def noLeadingZeros (bits: List Nat) : Prop :=
  bits = [0] ∨ (bits.length > 0 ∧ bits.head? = some 1)

method DecimalToBinary (n: Nat)
  return (binary: List Nat)
  ensures allBinaryDigits binary  -- All elements are 0 or 1
  ensures binaryToDecimal binary = n  -- The binary representation equals the decimal input
  ensures noLeadingZeros binary  -- No leading zeros (except for n=0)
  ensures binary.length > 0  -- Result is never empty
  do
  -- Special case: n = 0
  if n = 0 then
    return [0]
  else
    -- General case: n > 0
    -- Build binary representation by repeatedly dividing by 2
    let mut num := n
    let mut result : List Nat := []
    while num > 0
      invariant allBinaryDigits result
      invariant binaryToDecimal result + num * 2^(result.length) = n
      invariant n > 0
      invariant num > 0 → result.length > 0 ∨ num = n
      invariant num = 0 → result.head? = some 1
    do
      let remainder := num % 2
      result := remainder :: result  -- Prepend to get big-endian
      num := num / 2
    return result

----------------------------------------------------------
-- Refutation of a weak loop invariant (missing last line)
----------------------------------------------------------

open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)

-- Aristotle found this block to be false. Here is a proof of the negation:
theorem goal3'
(n : ℕ)
(num : ℕ)
(result : List ℕ)
(i : ℕ)
(result_1 : List ℕ)
(if_neg : ¬n = i)
(invariant_1 : ∀ b ∈ result_1, b = i ∨ b = 1)
(invariant_2 : List.foldl (fun acc bit => 2 * acc + bit) i result_1 + i * 2 ^ result_1.length = n)
(invariant_3 : i < n)
(i_1 : 0 = i ∧ result = result_1)
: result_1 = [i] ∨ i < result_1.length ∧ result_1.head? = some 1 :=
  by
    -- Wait, there's a mistake. We can actually prove the opposite.
    negate_state
    -- Proof starts here:
    -- Let's choose any $n$ greater than 1.
    use 3
    -- Let's choose any $num$ greater than 1.
    use 1
    -- Let's choose any $result$ and $result_1$ such that $result = result_1$ and $result_1 \neq [i]$.
    use [0, 1, 1], 0, [0, 1, 1]
    aesop

-- alternative way to show the refutation
theorem refute_goal :
  ∃ (n num i : ℕ) (result result_1 : List ℕ),
  n ≠ i ∧
    (∀ b ∈ result_1, b = i ∨ b = 1) ∧
      List.foldl (fun acc bit ↦ 2 * acc + bit) i result_1 + i * 2 ^ result_1.length = n ∧
        i < n ∧ (0 = i ∧ result = result_1) ∧ result_1 ≠ [i] ∧ (i < result_1.length → result_1.head? ≠ some 1) :=
  by
    use 3
    use 1
    use 0
    -- Let's choose any $result$ and $result_1$ such that $result = result_1$ and $result_1 \neq [i]$.
    use [0, 1, 1], [0, 1, 1]
    aesop

-- Then it is easy to fix the invariant


---------------------------------------------------------
-- The actual proof
---------------------------------------------------------

theorem goal1
(n : ℕ)
(if_neg : ¬n = 0)
(num : ℕ)
(result : List ℕ)
(invariant_1 : ∀ b ∈ result, b = 0 ∨ b = 1)
(invariant_2 : List.foldl (fun acc bit => 2 * acc + bit) 0 result + num * 2 ^ result.length = n)
(invariant_3 : 0 < n)
(invariant_4 : 0 < result.length ∨ num = n)
(if_pos : 0 < num)
: List.foldl (fun acc bit => 2 * acc + bit) (num % 2) result + num / 2 * 2 ^ (result.length + 1) = n :=
  by
    have h_foldl : ∀ (l : List ℕ), List.foldl (fun acc bit => 2 * acc + bit) (num % 2) l = List.foldl (fun acc bit => 2 * acc + bit) 0 l + num % 2 * 2 ^ l.length := by
      -- We proceed by induction on the list `l`.
      intro l
      induction' l using List.reverseRecOn with l ih;
      · -- The base case when the list is empty simplifies both sides of the equation to `num % 2`.
        simp [List.foldl];
      · -- By definition of foldl, we can split the operation into two parts: first processing `l` and then processing `[ih]`.
        simp [List.foldl_append, *];
        -- By simplifying, we can see that both sides of the equation are equal.
        ring;
    rw [ h_foldl ] ; ring;
    convert invariant_2 using 1 ; ring;
    -- By simplifying, we can see that both sides of the equation are equal.
    have h_simp : num * 2 ^ result.length = (num % 2 + num / 2 * 2) * 2 ^ result.length := by
      rw [ Nat.mod_add_div' ];
    rw [ h_simp ] ; ring

theorem goal2
(n : ℕ)
(num : ℕ)
(result : List ℕ)
(i : ℕ)
(result_1 : List ℕ)
(if_neg : ¬n = i)
(invariant_1 : ∀ b ∈ result_1, b = i ∨ b = 1)
(invariant_2 : List.foldl (fun acc bit => 2 * acc + bit) i result_1 + i * 2 ^ result_1.length = n)
(invariant_3 : i < n)
(invariant_5 : result_1.head? = some 1)
(i_1 : 0 = i ∧ result = result_1)
: i < result_1.length :=
  by
    -- If the length of `result` were zero, then the fold would be zero, contradicting `invariant_3`.
    by_contra h_len_zero
    aesop

theorem goal3
(n : ℕ)
(num : ℕ)
(result : List ℕ)
(i : ℕ)
(result_1 : List ℕ)
(if_neg : ¬n = i)
(invariant_1 : ∀ b ∈ result_1, b = i ∨ b = 1)
(invariant_2 : List.foldl (fun acc bit => 2 * acc + bit) i result_1 + i * 2 ^ result_1.length = n)
(invariant_3 : i < n)
(invariant_5 : result_1.head? = some 1)
(i_1 : 0 = i ∧ result = result_1)
: result_1 = [i] ∨ i < result_1.length :=
  by
    right
    by_contra h_len_zero
    aesop

---------------------------------------------------
-- Putting it all together
---------------------------------------------------

prove_correct DecimalToBinary by
  unfold noLeadingZeros binaryToDecimal allBinaryDigits
  loom_solve <;> simp_all
  · apply (goal1 n if_neg num result invariant_1 invariant_2 invariant_3 invariant_4 if_pos)
  · apply (goal2 n num result i result_1 if_neg invariant_1 invariant_2 invariant_3 invariant_5 i_1)
  · apply (goal3 n num result i result_1 if_neg invariant_1 invariant_2 invariant_3 invariant_5 i_1)
