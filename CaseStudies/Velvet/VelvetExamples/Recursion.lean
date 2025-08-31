import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open TotalCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

method simple_recursion (x : Nat) return (res: Nat)
  require True
  ensures res = x
  do
    if x = 0 then
      return 0
    else
      let pre_res ← simple_recursion (x - 1)
      return pre_res + 1

prove_correct simple_recursion by
  unfold simple_recursion
  loom_solve


method pickGreater (inp: Nat) return (res: Nat)
  ensures res > inp + 10
  do
    let ans :| ans > inp + 200
    return ans

prove_correct pickGreater by
  unfold pickGreater
  loom_solve

method pickGreaterN (n: Nat) return (res: Nat)
  ensures res >= n * 10
  do
    if n = 0 then
      return 0
    else
      let pre_res ← pickGreaterN (n - 1)
      let pre_res_big ← pickGreater pre_res
      return pre_res_big

prove_correct pickGreaterN by
  unfold pickGreaterN
  loom_solve

def fact (n: Nat): Nat :=
  if n = 0 then
    0
  else
    n * fact (n - 1)

method calc_fact (n: Nat) return (res: Nat)
  ensures fact n = res
  do
    if n = 0 then
      return 0
    else
      let mut i := 0
      let mut ans := 0
      let pre_res_n ← calc_fact (n - 1)
      while i < n
        invariant i <= n
        invariant i * pre_res_n = ans
        decreasing n - i
        do
          let pre_res ← calc_fact (n - 1)
          ans := ans + pre_res.1
          i := i + 1
      return ans

prove_correct calc_fact by
  unfold calc_fact
  loom_solve
  unfold fact at *
  aesop
  unfold fact
  aesop
  have : n = i := by omega
  simp [this]

/-method complex_measure_binsearch (l : Nat) (r: Nat) (x: Nat) return (res: Nat)
  require l * l ≤ x
  require x < r * r
  ensures res * res ≤ x
  ensures x ≤ (res + 1) * (res + 1)
  do
    if l + 1 = r then
      return l
    else
      let m := l + (r - l) / 2
      if m * m ≤ x then
        let pre_res_l ← complex_measure_binsearch m r x
        return pre_res_l
      else
        let pre_res_r ← complex_measure_binsearch l m x
        return pre_res_r-/

method pow2 (n: Nat) return (res: Nat)
  ensures 2 ^ n = res
  do
    if n = 0 then
      return 1
    else
      let mut i := 0
      let mut ans := 1
      while i < n
        invariant i <= n
        invariant 2 ^ i = ans
        decreasing n - i
        do
          let pre_res ← pow2 i
          ans := ans + pre_res.1
          i := i + 1
      return ans

set_option maxHeartbeats 2000000

lemma po2zer: 2 ^ 0 = 1 := by rfl

attribute [solverHint] Nat.two_pow_succ po2zer

prove_correct pow2 by
  unfold pow2
  loom_solve
