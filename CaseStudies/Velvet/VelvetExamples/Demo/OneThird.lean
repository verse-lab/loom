----------------------------------------------------
-- Example 2: Combining Velvet and non-trivial math
----------------------------------------------------

import Auto

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

import Mathlib.Tactic

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

open Filter Topology

/- noncomputable is needed because we use operations on ℝ -/
-- This function computers a sum of series
noncomputable method oneThird (n: Nat) return (res: ℝ)
  require n > 0
  ensures res = ∑ j ∈ Finset.range n, (j^2/n^3 : ℝ)
  do
    let mut res : Real := 0
    let mut i := 0
    while i < n
    invariant i <= n
    invariant res = ∑ j ∈ Finset.range i, (j^2/n^3 : ℝ)
    decreasing n - i
    do
      let x : ℝ := i / n
      res := res + (x * x) / n
      i := i + 1
    return res

grind_pattern Finset.sum_range_succ => Finset.sum (Finset.range (n + 1)) f
grind_pattern Finset.sum_range_zero => Finset.sum (Finset.range 0) f

/- half a second! -/
prove_correct oneThird by loom_solve

-- Proving the closed form for the sum of series: (n * (n + 1) * (2 * n + 1)) / 6
theorem tends_to_third' :
  Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), (Nat.cast (R := ℝ) i) ^ 2 / (n + 1) ^ 3) atTop (𝓝 (1 / 3)) := by
    -- We'll use the fact that $\sum_{i=0}^{n} i^2 = \frac{n(n+1)(2n+1)}{6}$ to simplify the expression.
    have h_sum : ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1), (i : ℝ) ^ 2) = (n * (n + 1) * (2 * n + 1) : ℝ) / 6 := by
      exact fun n => by induction n <;> norm_num [ Finset.sum_range_succ ] at * ; linarith;
    -- Substitute the formula for the sum of squares into the expression.
    suffices h_suff : Filter.Tendsto (fun n : ℕ => ((n * (n + 1) * (2 * n + 1) : ℝ) / 6) / ((n + 1) ^ 3)) Filter.atTop (𝓝 (1 / 3)) by
      -- Substitute the formula for the sum of squares into the expression and simplify.
      simp_all +decide [ ← Finset.sum_div ];
    -- We can divide the numerator and the denominator by $n^3$ and then take the limit as $n$ approaches infinity.
    suffices h_div : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) * (1 + 1 / (n : ℝ)) * (2 + 1 / (n : ℝ)) / 6) / ((1 + 1 / (n : ℝ)) ^ 3)) Filter.atTop (𝓝 (1 / 3)) by
      refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ div_eq_div_iff ] <;> first | positivity | field_simp [ -one_div, hn.ne' ] );
    convert Filter.Tendsto.div ( Filter.Tendsto.div_const ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) _ ) ( Filter.Tendsto.pow ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) _ ) _ using 2 <;> norm_num

-- Proving that (n * (n + 1) * (2 * n + 1)) / 6 tends to 1/3 when n goes to
-- infinity
--
/- main theorem: `oneThird (n + 1) |>.extract` is pure extraction of the `oneThird`
  Such extraction is guaranteed to converge and obey the same specification as
  the original `oneThird` as we have proven _total correctness_ of the `oneThird` method -/
lemma tends_to_third :
  Tendsto (fun n ↦ oneThird (n + 1) |>.extract) atTop (𝓝 (1 / 3)) := by
  apply Tendsto.congr _ tends_to_third'; intro n;
  erw [VelvetM.extract_spec _ _ (oneThird_correct _)] <;> grind
