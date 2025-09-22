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

section MaxElem

@[reducible]
def isMax (mx: Int) (arr: Array Int) := 
    forall i, ( h: i < arr.size ) -> mx >= (arr[i]'h)

method maxElem (arr: Array Int) return (res: Int)
  require arr.size > 0
  ensures isMax res arr
  do
    let mut i := 0
    let mut mx := arr[i]!
    i := i + 1
    while i < arr.size
    invariant 0 <= i ∧ i <= arr.size
    invariant forall j, j < i -> mx >= arr[j]!
    done_with i = arr.size
    do
      let elem := arr[i]!
      if elem > mx then
        mx := elem
      else
        mx := mx
      i := i + 1
    return mx

prove_correct maxElem by
  unfold isMax
  loom_solve
  · intro k hk
    have inv : forall j , j < i -> mx >= arr[j]! := by trivial
    have hISize : i = arr.size := by trivial
    aesop

end MaxElem
