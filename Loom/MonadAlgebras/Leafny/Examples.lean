
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
      mwp <;> aesop




-- #check WPGen.bind
      -- mwp
      -- { rintro ⟨k, s⟩; mwp; aesop }
      -- aesop
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


structure SpV (β) where
  ind: Array ℕ
  val: Array β
  size: ℕ
  h_sz_eq: ind.size = size ∧ val.size = size
  h_inc: ∀ (i j: ℕ), i < size → j < size →  i < j → ind[i]! < ind[j]!


instance : Inhabited (SpV β) where
  default :=
  { ind := #[],
    val := #[],
    size := 0,
    h_sz_eq := (by simp),
    h_inc := (fun i j h_i h_j i_lt_j => by trivial) }

def SpV.sumUpTo [Inhabited β] [AddCommMonoid ε] (spv : SpV β) (f : ℕ -> ℕ → β -> ε) (bound : ℕ) : ε :=
  ∑ i ∈ Finset.range bound, f i spv.ind[i]! spv.val[i]!

@[simp]
lemma SpV.sumUpToSucc [Inhabited β] [AddCommMonoid β] (spv : SpV β) (f : ℕ -> ℕ -> β -> β) (bound : ℕ) :
  spv.sumUpTo f (bound + 1) = (spv.sumUpTo f bound) + f bound spv.ind[bound]! spv.val[bound]! := by
  simp [sumUpTo]
  rw [@Finset.sum_range_succ]

method spmv
  (mut out: Array α)
  (arr: Array α)
  (spm : Array (SpV α)) return (u : Unit)
  ensures spm.size = outNew.size
  ensures ∀ i < spm.size, outNew[i]! = spm[i]!.sumUpTo (fun _ ind v => v * arr[ind]!) spm[i]!.size
  do
    out := Array.replicate spm.size 0
    let mut arrInd : Array ℕ := Array.replicate spm.size 0
    while_some i :| i < arrInd.size ∧ arrInd[i]! < spm[i]!.size
    invariant arrInd.size = spm.size
    invariant out.size = spm.size
    invariant ∀ i < arrInd.size, arrInd[i]! <= spm[i]!.size
    invariant ∀ i < arrInd.size, out[i]! = spm[i]!.sumUpTo (fun _ ind v => v * arr[ind]!) arrInd[i]!
    done_with ∀ i < arrInd.size, arrInd[i]! = spm[i]!.size
    do
      let ind := arrInd[i]!
      let vInd := spm[i]!.ind[ind]!
      let mVal := spm[i]!.val[ind]!
      let val := mVal * arr[vInd]!
      out[i] += val
      arrInd[i] += 1
    return
  correct_by by {
    simp; dsimp [spmv]
    mwp <;> aesop
    }
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

-- add_aesop_rules norm tactic (by omega)

instance [Inhabited β] [AddCommMonoid β] : GetElem (SpV β) ℕ β fun _ _ => True where
  getElem inst i _ :=
    match (Array.zip inst.ind inst.val).toList.find? fun (j, _) => j = i with
    | some pr => pr.2
    | none => 0

method VSpV
  (mut out: Array α)
  (arr: Array α)
  (spv: SpV α) return (u: Unit)
  ensures outNew.size = 1
  ensures outNew[0]! = spv.sumUpTo (fun _ ind v => v * arr[ind]!) spv.size
  do
    let mut ind := 0
    out := Array.replicate 1 0
    while ind ≠ spv.size
    invariant out.size = 1
    invariant ind ≤ spv.size
    invariant out[0]! = spv.sumUpTo (fun _ ind v  => v * arr[ind]!) ind
    done_with ind = spv.size
    do
      out[0] += spv.val[ind]! * arr[spv.ind[ind]!]!
      ind := ind + 1
    return
  correct_by by {
    simp; dsimp [VSpV]
    mwp <;> aesop (add safe (by omega))
   }

theorem getValSpV_eq (spv: SpV α) (j: ℕ) (h_ind: j < spv.size): spv[spv.ind[j]!] = spv.val[j]! := by
  simp [getElem]
  have just_case: List.find? (fun x ↦ decide (x.1 = spv.ind[j]!)) (spv.ind.toList.zip spv.val.toList) = some ((spv.ind[j]!, spv.val[j]!)):= by
    apply List.find?_eq_some_iff_getElem.mpr
    simp
    exists j
    rw [←spv.h_sz_eq.left] at h_ind
    constructor
    { simp [←getElem!_pos]
      rintro j₁ j₁_lt
      rw [spv.h_sz_eq.left] at h_ind
      have inj := spv.h_inc j₁ j (lt_trans j₁_lt h_ind) h_ind j₁_lt
      simp [lt_iff_le_and_ne.mp inj] }
    simp [h_ind]; rw [spv.h_sz_eq.right, ←spv.h_sz_eq.left]; simp [h_ind]
  simp [just_case]

theorem getValSpV_empty (spv: SpV α) (j: ℕ) (h_empty: ∀ i < spv.size, spv.ind[i]! ≠ j): spv[j] = 0 := by
  simp [getElem]
  have none_case: List.find? (fun x ↦ decide (x.1 = j)) (spv.ind.toList.zip spv.val.toList) = none := by
    apply List.find?_eq_none.mpr
    rintro x x_in; simp
    have zip_part := List.of_mem_zip x_in
    simp [List.mem_iff_get] at zip_part
    rcases zip_part.left with ⟨i, hi⟩
    have neq := h_empty i (have ilt := i.isLt; by simp [spv.h_sz_eq.left] at ilt; simp [ilt])
    rw [getElem!_pos spv.ind i.val i.isLt] at neq
    simp [hi] at neq
    simp [neq]
  simp [none_case]

theorem VSpV_correct_pure (out arr: Array α)
  (spv: SpV α)
  (h_b: ∀ i < spv.size, spv.ind[i]! < arr.size):
  out.size = 1 → out[0]! = spv.sumUpTo (fun _ ind v => v * arr[ind]!) spv.size →
    out[0]! = ∑ i ∈ Finset.range arr.size, spv[i] * arr[i]! := by
      intro sz sum_eq
      rw [sum_eq, SpV.sumUpTo]
      have ind_lemma: ∀ k, k ≤ arr.size →
        ∑ i ∈ Finset.range spv.size, (if spv.ind[i]! < k then spv.val[i]! * arr[spv.ind[i]!]! else 0) =
        ∑ i ∈ Finset.range k, spv[i] * arr[i]! := by
          intro k
          induction k with
          | zero =>
            simp
          | succ m hm =>
            intro lt_m
            simp [Finset.sum_range_succ]
            rw [←hm (by omega)]
            have splitted_sum:
              (∑ i ∈ Finset.range spv.ind.size, if spv.ind[i]! < m then spv.val[i]! * arr[spv.ind[i]!]! else 0) +
              (∑ i ∈ Finset.range spv.ind.size, if spv.ind[i]! = m then spv.val[i]! * arr[spv.ind[i]!]! else 0) =
              (∑ i ∈ Finset.range spv.ind.size, if spv.ind[i]! < m + 1 then spv.val[i]! * arr[spv.ind[i]!]! else 0) := by
                rw [←Finset.sum_add_distrib]
                rw [Finset.sum_congr (by rfl)]
                intro x hx
                by_cases h_eq_m : spv.ind[x]! = m <;> simp [h_eq_m]
                have miff : spv.ind[x]! < m ↔ spv.ind[x]! < m + 1 := by
                  constructor <;> rintro h_lt <;> omega
                simp [miff]
            rw [←spv.h_sz_eq.left, ←splitted_sum, add_left_cancel_iff.mpr]
            by_cases exists_i: ∃ i < spv.size, spv.ind[i]! = m
            { rcases exists_i with ⟨ind, h_ind⟩
              rw [← h_ind.right]
              have lemma_res := getValSpV_eq spv ind h_ind.left
              simp at lemma_res
              simp [lemma_res]
              have almost_zero : ∀ i ∈ Finset.range spv.ind.size, i ≠ ind →
                ((if spv.ind[i]! = spv.ind[ind]! then spv.val[i]! * arr[spv.ind[i]!]! else 0) = 0) := by
                  intro i i_inb i_not_ind
                  by_cases vind_eq : spv.ind[i]! = spv.ind[ind]!
                  { simp at i_inb
                    have i_sz: i < spv.size := by
                      rw [spv.h_sz_eq.left] at i_inb
                      exact i_inb
                    rcases lt_or_gt_of_ne i_not_ind with i_lt | inb_lt
                    { simp [Nat.lt_iff_le_and_ne.mp (spv.h_inc i ind i_sz h_ind.left i_lt)] }
                    have lt := Nat.lt_iff_le_and_ne.mp (spv.h_inc ind i h_ind.left i_sz inb_lt)
                    simp [vind_eq] at lt }
                  simp [vind_eq]
              have ind_inb: ind ∉ Finset.range spv.size →
                ((if spv.ind[ind]! = spv.ind[ind]! then spv.val[ind]! * arr[spv.ind[ind]!]! else 0) = 0) := by
                  intro ind_not_inb
                  simp at ind_not_inb
                  omega
              rw [←spv.h_sz_eq.left] at ind_inb
              simp [Finset.sum_eq_single ind almost_zero ind_inb] }
            simp at exists_i
            have h_getVal := getValSpV_empty spv m exists_i
            simp at h_getVal
            simp [h_getVal]
            apply Finset.sum_eq_zero
            rintro x hx
            by_cases h_eq: spv.ind[x]! = m <;> simp [h_eq]
            simp [←h_eq] at h_getVal
            simp at hx
            rw [spv.h_sz_eq.left] at hx
            simp [getValSpV_eq spv x hx] at h_getVal
            simp [h_getVal]
      have fin_lemma := ind_lemma arr.size (by rfl)
      rw [←fin_lemma]
      exact Finset.sum_congr (by rfl) fun i h_i => by aesop

theorem VSpV_correct_triple (out arr: Array α) (spv: SpV α):
  triple
    (∀ i < spv.size, spv.ind[i]! < arr.size)
    (VSpV out arr spv)
    fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
      outNew[0]! = ∑ i ∈ Finset.range arr.size, spv[i] * arr[i]! := by
      simp [triple]
      intro h_b
      apply wp_cons (VSpV out arr spv)
        fun ⟨u, ⟨outNew, PUnit.unit⟩⟩ =>
          (outNew.size = 1 ∧ outNew[0]! = spv.sumUpTo (fun x ind v ↦ v * arr[ind]!) spv.size)
      { rintro ⟨u, ⟨outNew⟩⟩; simp
        intro sz sum_eq
        exact VSpV_correct_pure outNew arr spv h_b sz sum_eq }
      simp [triple]
      have triple_true := VSpV_correct out arr spv
      simp [triple] at triple_true
      exact triple_true

theorem spmv_correct_triple (out arr: Array α) (spm: Array (SpV α)):
  triple
    (∀ i < spm.size, ∀ j < spm[i]!.size, spm[i]!.ind[j]! < arr.size)
    (spmv out arr spm)
    fun ⟨_, ⟨outNew, _⟩⟩ =>
      (∀ j < outNew.size, outNew[j]! = ∑ i ∈ Finset.range arr.size, spm[j]![i] * arr[i]!) := by
      simp [triple]
      intro h_b
      apply wp_cons
        (spmv out arr spm)
        fun ⟨_, ⟨outNew, _⟩⟩ =>
          ((spm.size = outNew.size) ∧ ∀ i < spm.size, outNew[i]! = spm[i]!.sumUpTo (fun _ ind v => v * arr[ind]!) spm[i]!.size)
      { simp; rintro ⟨_, ⟨outNew⟩⟩; simp
        intro sz_eq sum_eq j h_j
        have single_elem : #[outNew[j]!][0]! = outNew[j]! := by simp
        have single_th := VSpV_correct_pure
          (#[outNew[j]!])
          arr
          spm[j]!
          (h_b j (by rw [←sz_eq] at h_j; exact h_j))
          (by simp)
          (by simp [single_elem]; exact sum_eq j (by rw [←sz_eq] at h_j; exact h_j))
        simp [single_elem] at single_th
        simp [←single_th] }
      simp
      have triple_true := spmv_correct out arr spm
      simp [triple] at triple_true
      exact triple_true

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

        done_with mind = 0 do
          if arr[mind]! ≤ arr[mind - 1]! then
            let left := arr[mind - 1]!
            let right := arr[mind]!
            arr[mind - 1] := right
            arr[mind] :=  left
          mind := mind - 1
        n := n + 1
      return
  correct_by by {
    simp; dsimp [insertionSort]
    mwp
    -- any_goals aesop (add safe (by omega))
    stop sorry
   }

/-
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
-/
end insertionSort

section squareRoot

method sqrt (x: ℕ) return (res: ℕ)
  ensures res * res ≤ x ∧ ∀ i, i ≤ res → i * i ≤ x
  do
    if x = 0 then
      return 0
    else
      let mut i := 0
      while i * i ≤ x
      invariant ∀ j, j < i → j * j ≤ x
      done_with x < i * i
      do
        i := i + 1
      return i - 1
  correct_by by
  { simp [sqrt]
    mwp
    any_goals first | grind | aesop (add safe (by omega))
    have hx : 1 ≤ x := by omega
    have hx₁ : 1 ≤ x_1 := by false_or_by_contra; aesop
    exact left (x_1 - 1) (by omega)
    have hx : 1 ≤ x := by omega
    have hx₁ : 1 ≤ x_1 := by false_or_by_contra; aesop
    aesop (add safe (by omega)) }

end squareRoot
