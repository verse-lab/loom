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

method simple_recursion (x : Nat) return (res: Nat)
  require True
  ensures res = x
  do
    if x = 0 then
      return 0
    else
      let pre_res ← simple_recursion (x - 1)
      return pre_res.1 + 1

prove_correct simple_recursion by
  loom_solve


method pickGreater (inp: Nat) return (res: Nat)
  ensures res > inp + 10
  do
    let ans :| ans > inp + 200
    return ans

prove_correct pickGreater by
  loom_solve
  exists (inp + 201)
  omega

method pickGreaterN (n: Nat) return (res: Nat)
  ensures res >= n * 10
  do
    if n = 0 then
      return 0
    else
      let pre_res ← pickGreaterN (n - 1)
      let pre_res_big ← pickGreater pre_res.1
      return pre_res_big.1

prove_correct pickGreaterN by
  loom_solve

@[grind]
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
        invariant i * pre_res_n.1 = ans
        decreasing n - i
        do
          let pre_res ← calc_fact (n - 1)
          ans := ans + pre_res.1
          i := i + 1
      return ans

prove_correct calc_fact by
  loom_solve


method SimpleOption (x: Option Nat) return (res: Nat)
  ensures res > 0
  do
    let rs ← match x with
    | some re =>
      let s := re + 2
      pure s
    | none =>
      pure 1
    return rs

prove_correct SimpleOption by
  cases x <;> loom_solve

method SimpleList (li: List Nat) return (res: Nat)
  ensures res > 0
  do
    match li with
    | x :: xs =>
      let prev ← SimpleList xs
      return (prev.1 + x)
    | [] =>
      return 1

prove_correct SimpleList by
  loom_solve

@[reducible]
def contains (tree: mt1 β) (elem: β) :=
  match tree with
  | .Leaf res => res = elem
  | .Empty => False
  | .Node l r res => res = elem ∨ contains l elem ∨ contains r elem

@[reducible]
def ordered_tree [LT β] (tree: mt1 β) :=
  match tree with
  | .Leaf _ => True
  | .Empty => True
  | .Node l r elem => ordered_tree l ∧ ordered_tree r ∧
    (∀ x, contains l x → x < elem) ∧
    (∀ x, contains r x → x > elem)

set_option maxHeartbeats 2000000

method insertTree (tree: mt1 Nat) (elem: Nat) return (res: mt1 Nat)
  require ordered_tree tree
  ensures contains res elem
  ensures ordered_tree res
  ensures ∀ x, (x = elem ∨ contains tree x) ↔ contains res x
  do
    let rs ← match tree with
      | .Node l r el =>
        if el = elem then
          pure tree
        else
          if el < elem then
            let right_res ← insertTree r elem
            pure (.Node l right_res.1 el)
          else
            let left_res ← insertTree l elem
            pure (.Node left_res.1 r el)
      | .Leaf el =>
        if el = elem then
          pure tree
        else
          if el < elem then
            pure (.Node (.Leaf el) (.Empty) elem)
          else
            pure (.Node (.Empty) (.Leaf el) elem)
      | .Empty =>
        pure (.Leaf elem)
    return rs

prove_correct insertTree by
  cases tree <;> loom_solve

method complex_measure_binsearch (l : Nat) (r: Nat) (x: Nat) return (res: Nat)
  require l * l ≤ x
  require x < r * r
  ensures res * res ≤ x
  ensures x ≤ (res + 1) * (res + 1)
  do
    if l + 1 >= r then
      return l
    else
      let m := l + (r - l) / 2
      if m * m ≤ x then
        let pre_res_l ← complex_measure_binsearch m r x
        return pre_res_l.1
      else
        let pre_res_r ← complex_measure_binsearch l m x
        return pre_res_r.1

prove_correct complex_measure_binsearch by
  loom_solve
  {
    have eq: l * l < r * r := by grind
    have : l < r := by exact Nat.mul_self_lt_mul_self_iff.mp eq
    grind
  }
  -- have eq: l < r := by


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

-- lemma po2zer: 2 ^ 0 = 1 := by rfl

prove_correct pow2 by
  loom_solve
  rw [if_pos]; rfl
