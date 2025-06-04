
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
  correct_by by { sorry }
    -- simp; intros; dsimp [spmv]
    -- mwp
    -- { intros; mwp
    --   aesop
    --   }
    -- aesop }
/-
  v    = [ A 0 0 B 0 0 C ]
  vInd = [ 0     3     6 ]
  vVal = [ A     B     C ]

  u    = [ X Y Z W A B C  ]

  ensures out = Σ i < vInd.size, vVal.sumUpTo (fun j x => x * v[mInd[j]!]!) vVal.size

  ensures out = Σ i < N, v[i] * get vVal vInd i


  vInd = [ 0     3     6 ]
  vVal = [ A     B     C ]

  uInd = [ 0     2     5 ]
  uVal = [ A     B     C ]

-/
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

def sparse_dot_product(xInd, xVal, yInd, yVal):
    i, j = 0, 0
    result = 0.0
    while i < len(xInd) and j < len(yInd):
        if xInd[i] == yInd[j]:
            result += xVal[i] * yVal[j]
            i += 1
            j += 1
        elif xInd[i] < yInd[j]:
            i += 1
        else:
            j += 1
    return result

-/
end SpMV

section insertionSort

/-

Dafny code below for reference

method insertionSort(arr: array<int>)
  modifies arr
  ensures forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures multiset(arr[..]) == old(multiset(arr[..]))
{
  if arr.Length <= 1 {
    return;
  }
  var n := 1;
  while n != arr.Length
  invariant 0 <= n <= arr.Length
  invariant forall i, j :: 0 <= i < j <= n - 1 ==> arr[i] <= arr[j]
  invariant multiset(arr[..]) == old(multiset(arr[..]))
  {
    var mind := n;
    while mind != 0
    invariant 0 <= mind <= n
    invariant multiset(arr[..]) == old(multiset(arr[..]))
    invariant forall i, j :: 0 <= i < j <= n && (j != mind)==> arr[i] <= arr[j]
    {
      if arr[mind] <= arr[mind - 1] {
        arr[mind], arr[mind - 1] := arr[mind - 1], arr[mind];
      }
      mind := mind - 1;
    }
    n := n + 1;
  }
}
-/
add_aesop_rules norm tactic (by omega)

set_option maxHeartbeats 1000000

method insertionSort
  (mut arr: Array Nat) return (u: Unit)
  ensures forall i j, i ≤ j ∧ j < arr.size → arrNew[i]! ≤ arrNew[j]!
  -- ensures exists f : Nat → Nat, (forall j1 j2, j1 ≠ j2 → f j1 ≠ f j2) ∧ arr[i]! = arrNew[f i]!
  do
    let arr_size := arr.size
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ arr.size
      invariant arr.size = arr_size
      invariant 1 ≤ n ∧ n ≤ arr.size
      invariant forall i j, i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!
      done_with n = arr.size
      do
        let mut mind := n
        while mind ≠ 0
        invariant arr.size = arr_size
        invariant mind ≤ n
        invariant forall i j, i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!

        invariant 1 ≤ n ∧ n < arr.size
        invariant forall i j, i < j ∧ j <= n - 1 → arr[i]! ≤ arr[j]!

        done_with mind = 0 do
          if arr[mind]! ≤ arr[mind - 1]! then
            let left := arr[mind - 1]!
            let right := arr[mind]!
            arr[mind - 1] := right
            arr[mind] :=  left
          mind := mind - 1
        n := n + 1
      return
  correct_by by { sorry }

#exit
    simp
    dsimp [insertionSort]
    mwp
    { simp; rintro _ ⟨arr', mind'⟩; mwp
      { simp; rintro _ ⟨arr'', mind''⟩; mwp
        intro a_2
        simp_all only [zero_le, not_false_eq_true, implies_true, true_and, and_true, Array.size_modify,
          tsub_le_iff_right, Array.modify_get, ↓reduceIte, Nat.default_eq_zero]
        obtain ⟨left, right⟩ := a_2
        obtain ⟨left_1, right⟩ := right
        obtain ⟨left_2, right⟩ := right
        obtain ⟨left_3, right⟩ := right
        obtain ⟨left_3, right_1⟩ := left_3
        simp_all only [true_and, and_true, if_true_left]
        intro a_2
        split
        next h =>
          apply And.intro
          · (omega)
          · apply And.intro
            · intro i j a_3 a_4 a_5
              split
              next h_1 =>
                split
                next h_2 =>
                  subst h_2
                  split
                  next h_2 =>
                    split
                    next h_3 =>
                      subst h_3
                      simp_all only [lt_self_iff_false]
                    next h_3 => apply left_2 <;> omega
                  next h_2 =>
                    simp_all only [not_lt, nonpos_iff_eq_zero]
                    (omega)
                next h_2 =>
                  split
                  next h_3 =>
                    subst h_3
                    split
                    next h_3 =>
                      split
                      next h_4 =>
                        subst h_4
                        simp_all only [tsub_lt_self_iff, Nat.lt_one_iff, pos_of_gt, and_true]
                      next h_4 => apply left_2 <;> omega
                    next h_3 =>
                      simp_all only [not_lt, nonpos_iff_eq_zero]
                      (omega)
                  next h_3 =>
                    split
                    next h_4 =>
                      split
                      next h_5 =>
                        subst h_5
                        simp_all only
                        apply left_2 <;> omega
                      next h_5 => simp_all only [not_false_eq_true]
                    next h_4 =>
                      simp_all only [not_lt, nonpos_iff_eq_zero]
                      (omega)
              next h_1 => simp_all only [not_lt, zero_le]
            · intro i j a_3 a_4
              split
              next h_1 =>
                split
                next h_2 =>
                  subst h_2
                  split
                  next h_2 =>
                    split
                    next h_3 =>
                      subst h_3
                      simp_all only [lt_self_iff_false]
                    next h_3 =>
                      split
                      next h_4 =>
                        subst h_4
                        simp_all only [tsub_le_iff_right, Nat.sub_add_cancel]
                        (omega)
                      next h_4 => apply left_2 <;> omega
                  next h_2 =>
                    simp_all only [not_lt, nonpos_iff_eq_zero]
                    (omega)
                next h_2 =>
                  split
                  next h_3 =>
                    subst h_3
                    split
                    next h_3 =>
                      split
                      next h_4 =>
                        subst h_4
                        simp_all only [tsub_lt_self_iff, Nat.lt_one_iff, pos_of_gt, and_true]
                      next h_4 =>
                        split
                        next h_5 =>
                          subst h_5
                          simp_all only [not_false_eq_true, tsub_le_iff_right, Nat.sub_add_cancel, lt_self_iff_false]
                        next h_5 => apply left_2 <;> omega
                    next h_3 =>
                      simp_all only [not_lt, nonpos_iff_eq_zero]
                      (omega)
                  next h_3 =>
                    split
                    next h_4 =>
                      split
                      next h_5 =>
                        subst h_5
                        apply left_2 <;> omega
                      next h_5 =>
                        split
                        next h_6 =>
                          subst h_6
                          simp_all only [tsub_le_iff_right, Nat.sub_add_cancel]
                          apply left_2 <;> omega
                        next h_6 => simp_all only
                    next h_4 =>
                      simp_all only [not_lt, nonpos_iff_eq_zero]
                      (omega)
              next h_1 => simp_all only [not_lt, zero_le]
        next h =>
          simp_all only [not_le]
          apply And.intro
          · (omega)
          · intro i j a_3 a_4 a_5
            sorry
         }
       }
    --   simp; intros
    --   mwp
    --   {
    --     simp; intros
    --     mwp
    --     {
    --       simp; intros
    --       aesop
    --       omega
    --       {
    --         simp [Array.setIfInBounds]
    --         aesop
    --         {
    --           simp [Array.getElem!_eq_getD]
    --           simp [Array.getD_getElem?]
    --           simp [Array.getElem!_eq_getD] at h
    --           simp [Array.getD_getElem?] at h
    --           have small_case:
    --             i_1 = 0 ∧ j = 1 ∧ snd = 1 ∧ 1 < fst.size ∧ 0 < fst.size := by omega
    --           simp [small_case]
    --           simp [small_case] at h
    --           exact h
    --         }
    --         omega
    --         omega
    --       }
    --       omega
    --       have small_case: j = 1 ∧ i_1 = 0 ∧ snd = 1 := by omega
    --       simp [small_case]
    --       simp [small_case] at h
    --       exact Nat.le_of_lt h
    --     }
    --   }
    --   aesop
    --   omega
    -- }
    -- aesop
    -- have small_case: i_1 = 0 ∧ j = 0 := by omega
    -- simp [small_case]
    -- {
    --   exact Exists.intro
    --     (fun i => i)
    --     (by
    --       simp)
    -- }
    -- omega
  }

end insertionSort
