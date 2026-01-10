----------------------------------------------------
-- Example 3: Multi-Modal Proof
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
@[grind]
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

------------------------------------------------
-- Program verification
------------------------------------------------

theorem goal
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

-- macro_rules
--   | `(tactic|loom_solver) => `(tactic|skip)

prove_correct IsNonPrime by
  loom_solve; try simp_all
  apply (goal n i ret i_1 ret_1 if_neg invariant_1 invariant_2 invariant_3 done_1 i_2)
