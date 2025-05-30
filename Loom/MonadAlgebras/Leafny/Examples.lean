
import Lean
import Lean.Parser

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic

import Loom.MonadAlgebras.Leafny.Extension
import Loom.MonadAlgebras.Leafny.Syntax
import Loom.MonadAlgebras.Leafny.Common

open PartialCorrectness DemonicChoice

section Collection
class Collection (α : outParam (Type)) (κ : Type) where
  mem : α -> κ -> Prop
  [dec : DecidableRel mem]
  del : α -> κ -> κ
  mem_del {b a} k : mem b (del a k) = (mem b k ∧ b ≠ a)
  isEmpty : κ -> Prop
  [dec_isEmpty : DecidablePred isEmpty]
  isEmpty_prop : ∀ k, isEmpty k = ∀ x, ¬ mem x k

variable {α κ} [col : Collection α κ] [DecidableEq α]

instance : DecidableRel (Collection.mem (α := α) (κ := κ)) := Collection.dec
instance : DecidablePred (Collection.isEmpty (α := α) (κ := κ)) := Collection.dec_isEmpty

instance [DecidableEq α] : Collection α (List α) where
  mem := (· ∈ ·)
  del x k := List.filter (· ≠ x) k
  mem_del := by simp
  isEmpty := (List.isEmpty ·)
  isEmpty_prop := by simp [List.eq_nil_iff_forall_not_mem]

attribute [-simp] if_true_left Bool.if_true_left ite_eq_left_iff
attribute [loomLogicSimp] ite_self


method Collection.toSet (mut k : κ) return (s : α -> Bool)
  ensures ∀ x, s x = Collection.mem x k
  do
    let k₀ := k
    let mut s := fun _ => false
    while ¬ Collection.isEmpty k
    invariant ∀ x, Collection.mem x k₀ <-> s x ∨ Collection.mem x k
    done_with ∀ x, ¬ Collection.mem x k do
      let a :| Collection.mem a k
      k := del a k
      s := fun x => if x = a then true else s x
    return s
  correct_by
    by
      cases col; simp;
      dsimp [Collection.toSet]
      mwp
      { rintro ⟨k, s⟩; mwp; aesop }
      aesop

/--
info: DivM.res
  ⟨[(0, false),
    (1, true),
    (2, true),
    (3, false),
    (4, false),
    (5, true),
    (6, false),
    (7, false),
    (8, false),
    (9, false)], ⟨[], ()⟩⟩
-/
#guard_msgs in
#eval Collection.toSet [1,2,5] |>.run

end Collection

section SpMV
variable [Inhabited α] [Ring α]
method spmv
  (mInd : Array (Array ℕ))
  (mVal : Array (Array α))
  (v : Array α) (mut out : Array α) return (u : Unit)
  require mInd.size = mVal.size
  require ∀ i < mInd.size, mInd[i]!.size = mVal[i]!.size
  require out.size = mVal.size
  require ∀ i : ℕ, out[i]! = 0
  ensures ∀ i < mInd.size, outNew[i]! = mVal[i]!.sumUpTo (fun j x => x * v[mInd[i]![j]!]!) mInd[i]!.size
  do
    let mut arrInd : Array ℕ := Array.replicate mInd.size 0
    while_some i :| i < arrInd.size ∧ arrInd[i]! < mInd[i]!.size
    invariant arrInd.size = mVal.size
    invariant out.size = mVal.size
    invariant ∀ i < arrInd.size, arrInd[i]! <= (mInd[i]!).size
    invariant ∀ i < arrInd.size, out[i]! = mVal[i]!.sumUpTo (fun j x => x * v[mInd[i]![j]!]!) arrInd[i]!
    done_with ∀ i < arrInd.size, arrInd[i]! = mInd[i]!.size
    do
      let ind := arrInd[i]!
      let vInd := mInd[i]![ind]!
      let mVal := mVal[i]![ind]!
      let val := mVal * v[vInd]!
      out[i] += val
      arrInd[i] += 1
    return
  correct_by by {
    simp; intros; dsimp [spmv]
    mwp
    { intros; mwp
      aesop
      }
    aesop }


/-

step-by-step execution of the spmv method:

out mVal     mInd     v
0   [ A, B ] [ 0, 3 ] [ X, Y, Z, W ]
0   [ C, D ] [ 1, 2 ] [ X, Y, Z, W ]

arrInd out mVal     mInd     v
0       0  [ A, B ] [ 0, 3 ] [ X, Y, Z, W ]
0       0  [ C, D ] [ 1, 2 ] [ X, Y, Z, W ]

arrInd out  mVal     mInd     v
1       AX  [ A, B ] [ 0, 3 ] [ X, Y, Z, W ]
0       0   [ C, D ] [ 1, 2 ] [ X, Y, Z, W ]


arrInd out  mVal     mInd     v
1       AX  [ A, B ] [ 0, 3 ] [ X, Y, Z, W ]
1       CY  [ C, D ] [ 1, 2 ] [ X, Y, Z, W ]


arrInd out     mVal     mInd     v
2       AX+BW  [ A, B ] [ 0, 3 ] [ X, Y, Z, W ]
1       CY     [ C, D ] [ 1, 2 ] [ X, Y, Z, W ]

arrInd out     mVal     mInd     v
2       AX+BW  [ A, B ] [ 0, 3 ] [ X, Y, Z, W ]
2       CY+DZ  [ C, D ] [ 1, 2 ] [ X, Y, Z, W ]

explanation for sparse vector x sparse vector:

https://chatgpt.com/c/68392ce7-3bc0-800c-8b6b-0f4708014701

-/
end SpMV
