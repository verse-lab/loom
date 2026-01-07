----------------------------------------------------
-- Example 3: Certified synthesis
----------------------------------------------------

-- Spec: This program checks whether a given natural number is non-prime.
--
-- Comment (not part of the spec): The time complexity of this algorithm is
-- O(√n): we check for divisors up to the square root of n. The program quite
-- simple, but to verify its correctness, we need to prove a property:
--
--       n is prime ↔ n > 1 ∧ ∀ d, 2 ≤ d ≤ √n → n % d ≠ 0
--
-- It is obvious for people who know number theory, but is painful to formalise
-- it in a proof assistant.

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

-- Helper definition to count divisors of a natural number
-- This counts all positive divisors from 1 to n
def countDivisors (n: Nat) : Nat :=
  (List.range (n + 1)).filter (fun d => d > 0 ∧ n % d = 0) |>.length

-- Helper definition for prime numbers
-- A number is prime if and only if:
-- 1. It is greater than 1
-- 2. It has exactly 2 positive divisors (1 and itself)
def isPrime (n: Nat) : Prop :=
  n > 1 ∧ countDivisors n = 2

method IsNonPrime (n: Nat)
  return (result: Bool)
  ensures result ↔ ¬isPrime n
  do
    if n ≤ 1 then
      return true
    let mut i: Nat := 2
    let mut ret: Bool := false
    while i * i ≤ n
    invariant 2 ≤ i
    invariant (ret = false ↔ ∀ d, 2 ≤ d ∧ d < i → n % d ≠ 0)
    invariant (i - 1) * (i - 1) ≤ n
    do
      if n % i = 0 then
        ret := true
      i := i + 1
    return ret

---------------------------------------------------------
-- Testing the specification
---------------------------------------------------------

-- Test cases for specification validation
section TestCases

-- Test case 1: From problem description
def test1_n : Nat := 2
def test1_Expected : Bool := false

-- Test case 2: Zero (edge case - non-prime)
def test2_n : Nat := 0
def test2_Expected : Bool := true

-- Test case 3: One (edge case - non-prime by convention)
def test3_n : Nat := 1
def test3_Expected : Bool := true

-- Test case 4: Smallest composite number
def test4_n : Nat := 4
def test4_Expected : Bool := true

-- Test case 5: Small prime
def test5_n : Nat := 5
def test5_Expected : Bool := false

-- Test case 6: Composite number (perfect square)
def test6_n : Nat := 9
def test6_Expected : Bool := true

-- Test case 7: Larger prime
def test7_n : Nat := 17
def test7_Expected : Bool := false

-- Test case 8: Perfect square composite
def test8_n : Nat := 25
def test8_Expected : Bool := true

-- Test case 9: Large composite number
def test9_n : Nat := 652656516
def test9_Expected : Bool := true

-- Test case 10: Large prime number
def test10_n : Nat := 998244353
def test10_Expected : Bool := false

-- Test case 11: Another large composite (even number)
def test11_n : Nat := 1000000000
def test11_Expected : Bool := true

-- Test case 12: Semi-prime (product of two primes)
def test12_n : Nat := 15
def test12_Expected : Bool := true

-- Test case 13: Prime in mid-range
def test13_n : Nat := 97
def test13_Expected : Bool := false

-- Test case 14: Composite with multiple factors
def test14_n : Nat := 100
def test14_Expected : Bool := true

------------------------------------------------------
-- Verifying tests
------------------------------------------------------

-- Pre/Post Conditions
def ensures1 (n: Nat) (result: Bool) := result ↔ ¬isPrime n

def precondition (n: Nat) := True

def postcondition (n: Nat) (result: Bool) :=
  ensures1 n result

-- Recommend to validate: test cases 1, 2, 3, 4, 5, 8

-- test1
lemma test1_precondition :
  precondition test1_n := by
  exact?

lemma test1_postcondition :
  postcondition test1_n test1_Expected := by
  -- Since 2 is a prime number, ¬isPrime 2 is false.
  have h_prime : isPrime 2 := by
    -- We know that 2 is a prime number by definition.
    apply And.intro (by norm_num) (by native_decide);
  unfold test1_n test1_Expected postcondition ensures1; aesop;

-- test2
lemma test2_precondition :
  precondition test2_n := by
  exact?

lemma test2_postcondition :
  postcondition test2_n test2_Expected := by
  -- By definition of test2_n and test2_Expected, we have n = 0 and result = true.
  simp [postcondition, test2_n, test2_Expected];
  -- Since 0 is not greater than 1, it is not prime.
  simp [ensures1, isPrime]

-- test3
lemma test3_precondition :
  precondition test3_n := by
  -- The precondition is trivially true.
  simp [precondition]

lemma test3_postcondition :
  postcondition test3_n test3_Expected := by
  -- Since 1 is not prime, we have ¬isPrime 1.
  have h_not_prime : ¬isPrime 1 := by
    -- By definition, 1 is not a prime number.
    simp [isPrime];
  -- Since 1 is not prime, we have ¬isPrime 1, which satisfies the postcondition.
  apply Iff.intro;
  · -- Since the expected result is true, we can directly use h_not_prime to conclude that 1 is not prime.
    intro h_true
    exact h_not_prime;
  · aesop

-- test4
lemma test4_precondition :
  precondition test4_n := by
  exact?

lemma test4_postcondition :
  postcondition test4_n test4_Expected := by
  constructor;
  · -- By definition of `isPrime`, we need to show that `4` is not prime.
    unfold isPrime;
    native_decide +revert;
  · -- Since 4 is not prime, the result of the function should be true.
    simp [test4_Expected]

-- test5
lemma test5_precondition :
  precondition test5_n := by
  exact?

lemma test5_postcondition :
  postcondition test5_n test5_Expected := by
  -- Since 5 is prime, ¬isPrime 5 is false, which matches the result being false.
  simp [postcondition, test5_n, test5_Expected];
  -- Since 5 is prime, ¬isPrime 5 is false, which matches the result being false. Therefore, the proof is complete.
  simp [ensures1, isPrime];
  decide +kernel

-- test8
lemma test8_precondition :
  precondition test8_n := by
  exact?

lemma test8_postcondition :
  postcondition test8_n test8_Expected := by
  -- Apply the definition of Ensure to rewrite the goal in terms of the logical equivalence.
  unfold postcondition; unfold ensures1; unfold test8_n; unfold test8_Expected; simp +decide [isPrime];

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (n: Nat):
  precondition n →
  (∀ ret1 ret2,
    postcondition n ret1 →
    postcondition n ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if ret1 and ret2 both satisfy the postcondition, then they must both be equal to ¬isPrime n.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  have h_eq : ret1 = ¬isPrime n ∧ ret2 = ¬isPrime n := by
    bound;
  grind

------------------------------------------------
-- Program verification
------------------------------------------------

theorem goal1
(n : ℕ)
(if_pos : n ≤ 1)
: ¬isPrime n :=
  by
    -- Since $n \leq 1$, we have $n = 0$ or $n = 1$. In either case, $n$ is not greater than 1, so it cannot be prime.
    cases' n with n n <;> simp [isPrime];
    -- Since $n$ is a natural number, the only way $n + 1 \leq 1$ is if $n = 0$. But if $n = 0$, then $n + 1 = 1$, and the count of divisors of 1 is 1, not 2.
    aesop

theorem goal2
(n : ℕ)
(i : ℕ)
(ret : Bool)
(i_1 : ℕ)
(ret_1 : Bool)
(if_neg : 1 < n)
(invariant_1 : 2 ≤ i_1)
(invariant_2 : ret_1 = false ↔ ∀ (d : ℕ), 2 ≤ d → d < i_1 → ¬n % d = 0)
(invariant_3 : (i_1 - 1) * (i_1 - 1) ≤ n)
(done_1 : n < i_1 * i_1)
(i_2 : i = i_1 ∧ ret = ret_1)
: ret_1 = true ↔ ¬isPrime n :=
  by
    -- If ret_1 is true, then there exists a divisor d between 2 and i_1-1, making n not prime.
    have h_true : ret_1 = Bool.true → ¬isPrime n := by
      aesop;
      unfold isPrime at a; aesop;
      unfold countDivisors at right; contrapose! right; aesop;
      -- Since $w$ divides $n$, and $1$ and $n$ are also divisors of $n$, the list of divisors must contain at least these three elements.
      have h_divisors : 1 ∈ List.filter (fun d => 0 < d ∧ n % d = 0) (List.range (n + 1)) ∧ w ∈ List.filter (fun d => 0 < d ∧ n % d = 0) (List.range (n + 1)) ∧ n ∈ List.filter (fun d => 0 < d ∧ n % d = 0) (List.range (n + 1)) := by
        simp_all +decide [ List.mem_filter, List.mem_range ];
        exact ⟨ ⟨ by linarith, Nat.mod_one _ ⟩, ⟨ by nlinarith only [ left, left_1, left_2, invariant_3, Nat.sub_add_cancel ( by linarith : 1 ≤ i ) ], by linarith ⟩, by linarith ⟩;
      have h_divisors_card : List.toFinset (List.filter (fun d => 0 < d ∧ n % d = 0) (List.range (n + 1))) ⊇ {1, w, n} := by
        aesop_cat;
      have h_divisors_card : Finset.card (List.toFinset (List.filter (fun d => 0 < d ∧ n % d = 0) (List.range (n + 1)))) ≥ 3 := by
        refine' le_trans _ ( Finset.card_mono h_divisors_card );
        rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num;
        · nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ i ) ];
        · grind;
      exact h_divisors_card.not_lt ( lt_of_le_of_lt ( List.toFinset_card_le _ ) ( by aesop ) );
    -- If ret_1 is false, then by invariant_2, there are no divisors of n in the range 2 to i_1-1. Since n is less than i_1 squared, and i_1 is at least 2, this implies that n has no divisors other than 1 and itself. Hence, n is prime.
    have h_false : ret_1 = Bool.false → isPrime n := by
      intro h
      have h_no_divisors : ∀ d, 1 < d → d < n → ¬n % d = 0 := by
        intros d hd1 hd2 hd3;
        have h_div : d ≤ i_1 - 1 ∨ n / d ≤ i_1 - 1 := by
          exact Classical.or_iff_not_imp_left.2 fun h => by nlinarith [ Nat.div_mul_cancel ( Nat.dvd_of_mod_eq_zero hd3 ), Nat.sub_add_cancel ( by linarith : 1 ≤ i_1 ) ] ;
        bound;
        · exact invariant_2.mp rfl d hd1 ( by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ i ) ] ) hd3;
        · exact invariant_2.mp rfl ( n / d ) ( by nlinarith [ Nat.div_mul_cancel ( Nat.dvd_of_mod_eq_zero hd3 ) ] ) ( by omega ) ( Nat.mod_eq_zero_of_dvd <| Nat.div_dvd_of_dvd <| Nat.dvd_of_mod_eq_zero hd3 )
      have h_prime : Nat.Prime n := by
        exact Nat.prime_def_lt'.mpr ⟨ if_neg, fun d hd₁ hd₂ hd₃ => h_no_divisors d hd₁ hd₂ <| Nat.mod_eq_zero_of_dvd hd₃ ⟩
      exact (by
      constructor <;> aesop;
      -- Since n is prime, its only divisors are 1 and itself.
      have h_divisors : List.toFinset (List.filter (fun d => d > 0 ∧ n % d = 0) (List.range (n + 1))) = {1, n} := by
        ext d; aesop;
        · exact Classical.or_iff_not_imp_left.2 fun h => by have := Nat.dvd_of_mod_eq_zero right; rw [ Nat.dvd_prime h_prime ] at this; aesop;
        · linarith;
        · rw [ Nat.mod_one ];
        · grind;
      -- Since the Finset {1, n} has cardinality 2, we can conclude that the list's length is also 2.
      have h_card : List.length (List.filter (fun d => d > 0 ∧ n % d = 0) (List.range (n + 1))) = Finset.card (List.toFinset (List.filter (fun d => d > 0 ∧ n % d = 0) (List.range (n + 1)))) := by
        rw [ List.toFinset_card_of_nodup ];
        refine' List.Nodup.filter _ _;
        grind;
      exact h_card.trans ( h_divisors.symm ▸ by rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop ));
    grind

----------------------------------------------------------------
-- Putting it all together
----------------------------------------------------------------

prove_correct IsNonPrime by
  loom_solve <;> try simp_all
  · apply (goal1 n if_pos)
  · apply (goal2 n i ret i_1 ret_1 if_neg invariant_1 invariant_2 invariant_3 done_1 i_2)


end TestCases
