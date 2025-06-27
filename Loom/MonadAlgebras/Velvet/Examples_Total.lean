import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import Loom.MonadAlgebras.Velvet.Extension
import Loom.MonadAlgebras.Velvet.Syntax
import Loom.MonadAlgebras.Velvet.Common
import Loom.MonadAlgebras.Velvet.Tactic

open TotalCorrectness DemonicChoice

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 10
set_option auto.smt.solver.name "cvc5"
syntax (priority := high + 1) ident noWs "[" term "]" ":=" term : doElem
syntax (priority := high + 1) ident noWs "[" term "]" "+=" term : doElem

macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := TArray.set $idx $val $id:term)
  | `(doElem|$id:ident[$idx:term] += $val:term) =>
    `(doElem| $id:term := TArray.set $idx (($id:term)[$idx] + $val) $id:term)

section squareRoot

set_option trace.Loom true

method sqrt (x: ℕ) return (res: ℕ)
  require x > 8
  ensures res * res ≤ x ∧ ∀ i, i ≤ res → i * i ≤ x
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i ≤ x
      invariant ∀ j, j < i → j * j ≤ x
      decreasing x - i
      do
        i := i + 1
      return i - 1
prove_correct sqrt by
  dsimp [sqrt]
  velvet_solve

method sqrt_bn (x: ℕ) (bnd: ℕ) return (res: ℕ)
  require x < bnd * bnd
  ensures res * res ≤ x ∧ ∀ i, i ≤ res → i * i ≤ x
  do
    let mut l := 0
    let mut r := bnd
    while 1 < r - l
    invariant l * l ≤ x
    invariant x < r * r
    invariant ∀ i, i ≤ l → i * i ≤ x
    decreasing r - l
    do
      let m := (r + l) / 2
      if m * m ≤ x then
        l := m
      else
        r := m
    return l
prove_correct sqrt_bn by
  dsimp [sqrt_bn]
  velvet_solve!

end squareRoot
