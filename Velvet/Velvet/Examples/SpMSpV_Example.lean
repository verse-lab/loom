import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import Velvet.Extension
import Velvet.Syntax
import Velvet.Tactic
import Velvet.Std

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 10
set_option auto.smt.solver.name "cvc5"

attribute [solverHint] TArray.get_set TArray.size_set

section SpMV

attribute [local solverHint] TArray.replicate_size TArray.replicate_get

variable {arrNat} [ind_inst: TArray Nat arrNat]
variable {arrVal} [val_inst: TArray Int arrVal]


instance : Inhabited arrVal where
  default := val_inst.replicate 0 default

structure SpV (valTyp arrVal arrNat : outParam Type) [v_inst: TArray valTyp arrVal] [i_inst: TArray Nat arrNat] where
  ind: arrNat
  val: arrVal
  size: ℕ
  h_sz_eq: i_inst.size ind = size ∧ v_inst.size val = size
  h_inc: ∀ (i j: Nat), i < size → j < size →  i < j → ind[i] < ind[j]

class SpVT (valTyp arrVal arrNat : outParam Type) [v_inst: TArray valTyp arrVal] [i_inst: TArray Nat arrNat] (κ : Type) where
  ind: κ -> arrNat
  val: κ -> arrVal
  size: κ -> ℕ
  h_sz_eq: ∀ k, TArray.size (ind k) = size k ∧ TArray.size (val k) = size k
  h_inc: ∀ (k : κ) (i j: Nat), i < size k → j < size k →  i < j → TArray.get i (ind k) < TArray.get j (ind k)

attribute [local solverHint] SpVT.h_sz_eq SpVT.h_inc

export SpVT (ind val)

def sumUpTo {SpVAbs} [v_inst: TArray Int arrVal] [i_inst: TArray Nat arrNat]
  [SpV_inst: SpVT Int arrVal arrNat SpVAbs]
  (spv : SpVAbs)
  (v : arrVal) (bound : ℕ) : Int := ∑ i ∈ Finset.range bound, ((val spv)[i] * v[(ind spv)[i]])

@[solverHint]
lemma sumUpToSucc
  (SpV_inst : SpVT ℤ arrVal arrNat SpVAbs := by assumption)
  (spv : SpVAbs)
  (v : arrVal) (bound : ℕ) :
  sumUpTo spv v (bound + 1) = (sumUpTo spv v bound) +
    (TArray.get bound (SpVT.val spv) * (TArray.get (TArray.get bound (SpVT.ind spv)) v)) := by
  simp [sumUpTo]
  simp [@Finset.sum_range_succ, getElemE]

variable {SpVAbs} [SpV_inst : SpVT Int arrVal arrNat SpVAbs]
variable {arrSpV} [SpM_inst: TArray SpVAbs arrSpV]

instance : Inhabited (SpV Int arrVal arrNat) where
  default :=
  { ind := default,
    val := default,
    size := 0,
    h_sz_eq := (by simp [default, TArray.replicate_size]),
    h_inc := (fun i j h_i h_j i_lt_j => by simp [default]; omega) }
@[solverHint]
lemma sumUpTo0
  (spv : SpVAbs) (v : arrVal) :
  sumUpTo spv v 0 = 0 := by
  simp [sumUpTo]


method spmv
  (mut out: arrVal)
  (arr: arrVal)
  (spm : arrSpV) return (u : Unit)
  ensures size spm = size outNew
  ensures ∀ i < size spm, outNew[i] = sumUpTo spm[i] arr (SpVT.size spm[i])
  do
    out := TArray.replicate (TArray.size spm) 0
    let mut arrInd : arrNat := TArray.replicate (TArray.size spm) 0
    while_some i :| i < TArray.size arrInd ∧ arrInd[i] < SpVT.size spm[i]
    invariant TArray.size arrInd = TArray.size spm
    invariant TArray.size out = TArray.size spm
    invariant ∀ i < TArray.size arrInd, arrInd[i] <= SpVT.size spm[i]
    invariant ∀ i < TArray.size arrInd, out[i] = sumUpTo spm[i] arr arrInd[i]
    done_with ∀ i < TArray.size arrInd, arrInd[i] = SpVT.size spm[i]
    do
      let ind := arrInd[i]
      let vInd := (SpVT.ind spm[i])[ind]
      let mVal := (SpVT.val spm[i])[ind]
      let val := mVal * arr[vInd]
      out[i] += val
      arrInd[i] += 1
    return

prove_correct spmv by
  dsimp [spmv]
  velvet_solve


def toList [arr_inst: TArray ε τ] (arr: τ): List ε :=
  (List.range (arr_inst.size arr)).map (fun i => arr_inst.get i arr)

instance: GetElem SpVAbs Nat Int fun _ _ => True where
  getElem inst i _ :=
    match (List.zip (toList (SpVT.ind inst)) (toList (SpVT.val inst))).find? fun (j, _) => j = i with
    | some pr => pr.2
    | none => 0


method VSpV
  (mut out: arrVal)
  (arr: arrVal)
  (spv: SpVAbs) return (u: Unit)
  ensures size outNew = 1
  ensures outNew[0] = sumUpTo spv arr (SpVT.size spv)
  do
    let mut ind := 0
    out := val_inst.replicate 1 0
    while ind ≠ SpVT.size spv
    invariant size out = 1
    invariant ind ≤ SpVT.size spv
    invariant out[0] = sumUpTo spv arr ind
    done_with ind = SpVT.size spv
    do
      out[0] += (SpVT.val spv)[ind] * arr[(SpVT.ind spv)[ind]]
      ind := ind + 1
    return

prove_correct VSpV by
  dsimp [VSpV]
  velvet_solve

theorem getValSpV_eq (spv: SpVAbs) (j: ℕ) (h_ind: j < SpVT.size spv): spv[(SpVT.ind spv)[j]] = (SpVT.val spv)[j] := by
  simp [getElem]
  have just_case:
    List.find?
      (fun x ↦ decide (x.1 = (SpVT.ind spv)[j]))
      (List.zip (toList (SpVT.ind spv)) (toList (SpVT.val spv))) = some (((SpVT.ind spv)[j], (SpVT.val spv)[j])):= by
    apply List.find?_eq_some_iff_getElem.mpr
    simp
    exists j
    rw [←(SpVT.h_sz_eq spv).left] at h_ind
    constructor
    { simp [toList]
      simp [GetElem.getElem]
      rintro j₁ j₁_lt
      rw [(SpVT.h_sz_eq spv).left] at h_ind
      have inj := SpVT.h_inc spv j₁ j (lt_trans j₁_lt h_ind) h_ind j₁_lt
      simp [GetElem.getElem] at inj
      simp [lt_iff_le_and_ne.mp inj] }
    simp [toList, h_ind]; rw [(SpVT.h_sz_eq spv).right, ←(SpVT.h_sz_eq spv).left]; simp [h_ind]
  simp [GetElem.getElem] at just_case
  simp [just_case]


theorem getValSpV_empty (spv: SpVAbs) (j: ℕ) (h_empty: ∀ i < SpVT.size spv, (SpVT.ind spv)[i] ≠ j): spv[j] = 0 := by
  simp [getElem]
  have none_case: List.find? (fun x ↦ decide (x.1 = j)) (List.zip (toList (SpVT.ind spv)) (toList (SpVT.val spv))) = none := by
    apply List.find?_eq_none.mpr
    rintro x x_in; simp
    have zip_part := List.of_mem_zip x_in
    simp [List.mem_iff_get] at zip_part
    rcases zip_part.left with ⟨i, hi⟩
    have neq := h_empty i (have ilt := i.isLt; by simp [toList, (SpVT.h_sz_eq spv).left] at ilt; simp [ilt])
    simp [toList] at hi
    simp [GetElem.getElem] at neq
    simp [hi] at neq
    simp [neq]
  simp [none_case]

theorem VSpV_correct_pure (out: arrVal) (arr: arrVal)
  (spv: SpVAbs)
  (h_b: ∀ i < SpVT.size spv, (SpVT.ind spv)[i] < size arr):
  size out = 1 → out[0] = sumUpTo spv arr (SpVT.size spv) →
    out[0] = ∑ i ∈ Finset.range (size arr), spv[i] * arr[i] := by
      intro sz sum_eq
      rw [sum_eq, sumUpTo]
      have ind_lemma: ∀ k, k ≤ size arr →
        ∑ i ∈ Finset.range (SpVT.size spv), (if (SpVT.ind spv)[i] < k then (SpVT.val spv)[i] * arr[(SpVT.ind spv)[i]] else 0) =
        ∑ i ∈ Finset.range k, spv[i] * arr[i] := by
          intro k
          induction k with
          | zero =>
            simp
          | succ m hm =>
            intro lt_m
            simp [Finset.sum_range_succ]
            rw [←hm (by omega)]
            have splitted_sum:
              (∑ i ∈ Finset.range (ind_inst.size (SpVT.ind spv)), if (SpVT.ind spv)[i] < m then (SpVT.val spv)[i] * arr[(SpVT.ind spv)[i]] else 0) +
              (∑ i ∈ Finset.range (ind_inst.size (SpVT.ind spv)), if (SpVT.ind spv)[i] = m then (SpVT.val spv)[i] * arr[(SpVT.ind spv)[i]] else 0) =
              (∑ i ∈ Finset.range (ind_inst.size (SpVT.ind spv)), if (SpVT.ind spv)[i] < m + 1 then (SpVT.val spv)[i] * arr[(SpVT.ind spv)[i]] else 0) := by
                rw [←Finset.sum_add_distrib]
                rw [Finset.sum_congr (by rfl)]
                intro x hx
                by_cases h_eq_m : (SpVT.ind spv)[x] = m <;> simp [h_eq_m]
                have miff : (SpVT.ind spv)[x] < m ↔ (SpVT.ind spv)[x] < m + 1 := by
                  constructor <;> rintro h_lt <;> omega
                simp [miff]
            rw [←(SpVT.h_sz_eq spv).left, ←splitted_sum, add_left_cancel_iff.mpr]
            by_cases exists_i: ∃ i < SpVT.size spv, (SpVT.ind spv)[i] = m
            { rcases exists_i with ⟨ind, h_ind⟩
              rw [← h_ind.right]
              have lemma_res := getValSpV_eq spv ind h_ind.left
              simp at lemma_res
              simp [lemma_res]
              have almost_zero : ∀ i ∈ Finset.range (ind_inst.size (SpVT.ind spv)), i ≠ ind →
                ((if (SpVT.ind spv)[i] = (SpVT.ind spv)[ind] then (SpVT.val spv)[i] * arr[(SpVT.ind spv)[i]] else 0) = 0) := by
                  intro i i_inb i_not_ind
                  by_cases vind_eq : (SpVT.ind spv)[i] = (SpVT.ind spv)[ind]
                  { simp at i_inb
                    have i_sz: i < SpVT.size spv := by
                      rw [(SpVT.h_sz_eq spv).left] at i_inb
                      exact i_inb
                    rcases lt_or_gt_of_ne i_not_ind with i_lt | inb_lt
                    { simp [getElem, Nat.lt_iff_le_and_ne.mp (SpVT.h_inc spv i ind i_sz h_ind.left i_lt)] }
                    have lt := Nat.lt_iff_le_and_ne.mp (SpVT.h_inc spv ind i h_ind.left i_sz inb_lt)
                    simp [getElem] at vind_eq
                    simp [vind_eq] at lt }
                  simp [vind_eq]
              have ind_inb: ind ∉ Finset.range (SpVT.size spv) →
                ((if (SpVT.ind spv)[ind] = (SpVT.ind spv)[ind] then (SpVT.val spv)[ind] * arr[(SpVT.ind spv)[ind]] else 0) = 0) := by
                  intro ind_not_inb
                  simp at ind_not_inb
                  omega
              rw [←(SpVT.h_sz_eq spv).left] at ind_inb
              simp [Finset.sum_eq_single ind almost_zero ind_inb] }
            simp at exists_i
            have h_getVal := getValSpV_empty spv m exists_i
            simp at h_getVal
            simp [h_getVal]
            apply Finset.sum_eq_zero
            rintro x hx
            by_cases h_eq: (SpVT.ind spv)[x] = m <;> simp [h_eq]
            simp [←h_eq] at h_getVal
            simp at hx
            rw [(SpVT.h_sz_eq spv).left] at hx
            simp [getValSpV_eq spv x hx] at h_getVal
            simp [h_getVal]
      have fin_lemma := ind_lemma (size arr) (by rfl)
      rw [←fin_lemma]
      exact Finset.sum_congr (by rfl) fun i h_i => by aesop

theorem VSpV_correct_triple (out: arrVal) (arr: arrVal) (spv: SpVAbs):
  triple
    (∀ i < SpVT.size spv, (SpVT.ind spv)[i] < size arr)
    (VSpV out arr spv)
    fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
      outNew[0] = ∑ i ∈ Finset.range (size arr), spv[i] * arr[i] := by
      simp [triple]
      intro h_b
      apply wp_cons (VSpV out arr spv)
        fun ⟨u, ⟨outNew, PUnit.unit⟩⟩ =>
          (outNew[0] = sumUpTo spv arr (SpVT.size spv) ∧ size outNew = 1)
      { rintro ⟨u, ⟨outNew⟩⟩; simp
        intro sum_eq sz
        exact VSpV_correct_pure outNew arr spv h_b sz sum_eq }
      simp [triple]
      have triple_true := VSpV_correct out arr spv
      simp [triple, WithName] at triple_true
      exact triple_true

theorem spmv_correct_triple (out: arrVal) (arr: arrVal) (spm: arrSpV):
  triple
    (∀ i < size spm, ∀ j < (SpVT.size spm[i]), (SpVT.ind spm[i])[j] < size arr)
    (spmv out arr spm)
    fun ⟨_, ⟨outNew, _⟩⟩ =>
      (∀ j < size outNew, outNew[j] = ∑ i ∈ Finset.range (size arr), spm[j][i] * arr[i]) := by
      simp [triple]
      intro h_b
      apply wp_cons
        (spmv out arr spm)
        fun ⟨_, ⟨outNew, _⟩⟩ =>
          ((∀ i < size spm, outNew[i] = sumUpTo spm[i] arr (SpVT.size spm[i])) ∧ size spm = size outNew)
      { simp; rintro ⟨_, ⟨outNew⟩⟩; simp
        intro sum_eq sz_eq j h_j
        have single_elem : (val_inst.replicate 1 outNew[j])[0] = outNew[j] := by
          have replicate_get := val_inst.replicate_get 1 outNew[j] 0 (by simp)
          simp [getElem] at replicate_get
          simp [getElem, replicate_get]
        have single_th := VSpV_correct_pure
          (val_inst.replicate 1 outNew[j])
          arr
          spm[j]
          (h_b j (by rw [←sz_eq] at h_j; exact h_j))
          (by simp [val_inst.replicate_size])
          (by simp [single_elem]; exact sum_eq j (by rw [←sz_eq] at h_j; exact h_j))
        simp [single_elem] at single_th
        simp [←single_th] }
      simp
      have triple_true := spmv_correct out arr spm
      simp [triple] at triple_true
      exact triple_true

def spv_dot [SpV_inst: SpVT ℤ arrVal arrNat SpVAbs_p] (spv1 spv2: SpVAbs_p) (pnt1 pnt2: ℕ): Int :=
  if (SpVT.size spv1) ≤ pnt1 ∨ (SpVT.size spv2) ≤ pnt2 then
    0
  else
    if (SpVT.ind spv1)[pnt1] = (SpVT.ind spv2)[pnt2] then
      (SpVT.val spv1)[pnt1] * (SpVT.val spv2)[pnt2] + spv_dot spv1 spv2 (pnt1 + 1) (pnt2 + 1)
    else
      if (SpVT.ind spv1)[pnt1] < (SpVT.ind spv2)[pnt2] then
        spv_dot spv1 spv2 (pnt1 + 1) pnt2
      else
        spv_dot spv1 spv2 pnt1 (pnt2 + 1)
  termination_by ((SpVT.size spv1) + (SpVT.size spv2) - pnt1 - pnt2)

@[solverHint]
lemma spv_dot_eq
  (SpV_inst : SpVT ℤ arrVal arrNat SpVAbs_p := by assumption)
  (spv1 spv2: SpVAbs_p) (pnt1 pnt2: ℕ) (prev: Int):
  prev + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0 →
    TArray.get pnt1 (SpVT.ind spv1) = TArray.get pnt2 (SpVT.ind spv2) →
    pnt1 < SpVT.size spv1 →
    pnt2 < SpVT.size spv2 →
    prev + TArray.get pnt1 (SpVT.val spv1) * TArray.get pnt2 (SpVT.val spv2) + spv_dot spv1 spv2 (pnt1 + 1) (pnt2 + 1) = spv_dot spv1 spv2 0 0 := by
      intro sum_eq ind_eq inb1 inb2
      rw [spv_dot] at sum_eq
      have neq: ¬(SpVT.size spv1 ≤ pnt1 ∨ SpVT.size spv2 ≤ pnt2) := by omega
      try simp only [loomAbstractionSimp] at *
      simp [neq, ind_eq] at sum_eq
      rw [←add_assoc] at sum_eq
      exact sum_eq

@[solverHint]
theorem spv_dot_lt
  (SpV_inst : SpVT ℤ arrVal arrNat SpVAbs_p := by assumption)
  (spv1 spv2: SpVAbs_p) (pnt1 pnt2: ℕ) (prev: Int):
  prev + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0 →
  TArray.get pnt1 (SpVT.ind spv1) < TArray.get pnt2 (SpVT.ind spv2) →
  pnt1 < SpVT.size spv1 → pnt2 < SpVT.size spv2 →
    prev + spv_dot spv1 spv2 (pnt1 + 1) pnt2 = spv_dot spv1 spv2 0 0 := by
      intro sum_eq ind_lt inb1 inb2
      rw [spv_dot] at sum_eq
      have neq: ¬(SpVT.size spv1 ≤ pnt1 ∨ SpVT.size spv2 ≤ pnt2) := by omega
      try simp only [loomAbstractionSimp] at *
      simp [neq, ind_lt] at sum_eq
      simp [lt_iff_le_and_ne.mp ind_lt] at sum_eq
      exact sum_eq

@[solverHint]
theorem spv_dot_gt
  (SpV_inst : SpVT ℤ arrVal arrNat SpVAbs_p := by assumption)
  (spv1 spv2: SpVAbs_p) (pnt1 pnt2: ℕ) (prev: Int) :
  prev + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0 →
  TArray.get pnt2 (SpVT.ind spv2) ≤ TArray.get pnt1 (SpVT.ind spv1) →
  TArray.get pnt1 (SpVT.ind spv1) ≠ TArray.get pnt2 (SpVT.ind spv2) →
  pnt1 < SpVT.size spv1 → pnt2 < SpVT.size spv2 →
    prev + spv_dot spv1 spv2 pnt1 (pnt2 + 1) = spv_dot spv1 spv2 0 0 := by
      intro sum_eq ind_le ind_neq inb1 inb2
      rw [spv_dot] at sum_eq
      have neq: ¬(SpVT.size spv1 ≤ pnt1 ∨ SpVT.size spv2 ≤ pnt2) := by omega
      try simp only [loomAbstractionSimp] at *
      simp [neq, ind_neq, ind_le] at sum_eq
      have ilt: ¬((SpVT.ind spv1)[pnt1] < (SpVT.ind spv2)[pnt2]) := by
        try simp only [loomAbstractionSimp] at *
        omega
      try simp only [loomAbstractionSimp] at *
      simp [ilt] at sum_eq
      exact sum_eq

@[solverHint]
theorem spv_dot_exh
  (SpV_inst : SpVT ℤ arrVal arrNat SpVAbs_p := by assumption)
  (spv1 spv2: SpVAbs_p) (pnt1 pnt2: ℕ):
  pnt1 = SpVT.size spv1 ∨ pnt2 = SpVT.size spv2 → spv_dot spv1 spv2 pnt1 pnt2 = 0 := by
    intro exh
    rw [spv_dot]
    by_cases triv: SpVT.size spv1 ≤ pnt1 ∨ SpVT.size spv2 ≤ pnt2 <;> simp [triv]
    omega

theorem spv_dot_pure_gen (spv1 spv2: SpVAbs) (n pnt1 pnt2: ℕ)
  (sz1: ∀ i < SpVT.size spv1, (SpVT.ind spv1)[i] < n)
  (sz2: ∀ i < SpVT.size spv2, (SpVT.ind spv2)[i] < n):
  spv_dot spv1 spv2 pnt1 pnt2 =
    ∑ i ∈ Finset.range n,
      if max
        (if SpVT.size spv1 ≤ pnt1 then n else (SpVT.ind spv1)[pnt1])
        (if SpVT.size spv2 ≤ pnt2 then n else (SpVT.ind spv2)[pnt2]) ≤ i then
        spv1[i] * spv2[i]
      else
        0 := by
  fun_induction spv_dot spv1 spv2 pnt1 pnt2 with
  | case1 p1 p2 h =>
    rw [spv_dot]
    rw [if_pos h]
    have all_zero: (∀ x ∈ Finset.range n, (if max (if SpVT.size spv1 ≤ p1 then n else (SpVT.ind spv1)[p1]) (if SpVT.size spv2 ≤ p2 then n else (SpVT.ind spv2)[p2]) ≤ x then spv1[x] * spv2[x] else 0) = 0) := by
      intro x hx
      simp [h]
      rcases h with ob1 | ob2
      { simp [ob1]
        simp at hx
        simp [hx] }
      simp [ob2]
      simp at hx
      simp [hx]
    rw [Finset.sum_eq_zero all_zero]
  | case2 p1 p2 h1 eq ih =>
    rw [spv_dot, if_neg h1, if_pos eq, ih, ←getValSpV_eq spv1 p1 (by omega), ←getValSpV_eq spv2 p2 (by omega)]
    have sum_eq_single:
      ∑ i ∈ Finset.range n, (if i = (SpVT.ind spv1)[p1] then spv1[(SpVT.ind spv1)[p1]] * spv2[(SpVT.ind spv1)[p1]] else 0) = (if (SpVT.ind spv1)[p1] = (SpVT.ind spv1)[p1] then spv1[(SpVT.ind spv1)[p1]] * spv2[(SpVT.ind spv1)[p1]] else 0) := by
      have hb: ∀ i ∈ Finset.range n, i ≠ (SpVT.ind spv1)[p1] → ((if i = (SpVT.ind spv1)[p1] then spv1[(SpVT.ind spv1)[p1]] * spv2[(SpVT.ind spv1)[p1]] else 0) = 0) := by
        intro i hi iq
        simp at hi
        simp [iq]
      have hc: (SpVT.ind spv1)[p1] ∉ Finset.range n → ((if (SpVT.ind spv1)[p1] = (SpVT.ind spv1)[p1] then spv1[(SpVT.ind spv1)[p1]] * spv2[(SpVT.ind spv1)[p1]] else 0) = 0) := by
        intro nin
        simp at nin
        have bnd := sz1 p1 (by omega)
        omega
      apply Finset.sum_eq_single (SpVT.ind spv1)[p1] hb hc
    simp at sum_eq_single
    rw [←eq, ←sum_eq_single]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr
    { rfl }
    intro x hx
    simp at hx
    have h2: ¬SpVT.size spv1 ≤ p1 ∧ ¬SpVT.size spv2 ≤ p2 := by omega
    simp [h2]
    have hnx: ¬(n ≤ x) := by simp [hx]
    by_cases xeq: x = (SpVT.ind spv1)[p1] <;> simp [xeq]
    { intro in1 in2
      by_cases edg1: SpVT.size spv1 ≤ p1 + 1 <;> simp [edg1] at in1
      { omega }
      have p1lt := (SpVT.h_inc spv1) p1 (p1 + 1) (by omega) (by omega) (by simp)
      simp [getElem] at in1
      omega }
    have outb_lemma (spv: SpVAbs) (pos: ℕ) (hsz: 1 ≤ SpVT.size spv) (hb: (SpVT.ind spv)[SpVT.size spv - 1] < pos): spv[pos] = 0 := by
      by_cases ex: ∃ i < SpVT.size spv, (SpVT.ind spv)[i] = pos
      { rcases ex with ⟨i, hbi, hi⟩
        by_cases heq: i = SpVT.size spv - 1
        { simp [heq] at hi
          omega }
        have contra := (SpVT.h_inc spv) i (SpVT.size spv - 1) (by omega) (by omega) (by omega)
        simp [getElem] at hb
        simp [getElem] at hi
        omega }
      simp at ex
      simp [getValSpV_empty spv pos ex]
    by_cases edg1: SpVT.size spv1 ≤ p1 + 1 <;> simp [edg1]
    { simp [hnx]
      have p1eq : p1 = SpVT.size spv1 - 1 := by omega
      by_cases lex: (SpVT.ind spv1)[p1] ≤ x <;> simp [lex]
      have ltx: (SpVT.ind spv1)[p1] < x := by omega
      simp [p1eq] at ltx
      simp [outb_lemma spv1 x (by omega) ltx] }
    by_cases edg2: SpVT.size spv2 ≤ p2 + 1 <;> simp [edg2]
    { simp [hnx]
      by_cases lex: (SpVT.ind spv1)[p1] ≤ x <;> simp [lex]
      have ltx: (SpVT.ind spv1)[p1] < x := by omega
      have p2eq: p2 = SpVT.size spv2 - 1 := by omega
      simp [eq, p2eq] at ltx
      simp [outb_lemma spv2 x (by omega) ltx] }
    by_cases val: (SpVT.ind spv1)[p1 + 1] ≤ x ∧ (SpVT.ind spv2)[p2 + 1] ≤ x <;> simp [val]
    { have inc: (SpVT.ind spv1)[p1] < (SpVT.ind spv1)[p1 + 1] := (SpVT.h_inc spv1) p1 (p1 + 1) (by omega) (by omega) (by simp)
      simp [le_of_lt (lt_of_lt_of_le inc val.left)] }
    by_cases xb: (SpVT.ind spv1)[p1] ≤ x <;> simp [xb]
    have ltx: (SpVT.ind spv1)[p1] < x := by omega
    simp at val
    have interm_lemma (spv: SpVAbs) (pos idx: ℕ) (hsz: idx + 1 < SpVT.size spv) (inter: (SpVT.ind spv)[idx] < pos ∧ pos < (SpVT.ind spv)[idx + 1]): spv[pos] = 0 := by
      by_cases ex: ∃ i < SpVT.size spv, (SpVT.ind spv)[i] = pos
      { rcases ex with ⟨i, hbi, hi⟩
        have lt_lemma (i1 i2: ℕ) (hi1: i1 < SpVT.size spv) (hi2: i2 < SpVT.size spv): (SpVT.ind spv)[i1] < (SpVT.ind spv)[i2] → i1 < i2 := by
          intro hlt
          by_cases contra_lt: i2 < i1
          { have inc := SpVT.h_inc spv i2 i1 hi2 hi1 contra_lt
            simp [getElem] at hlt
            omega }
          by_cases contra_eq: i1 = i2
          { simp [contra_eq] at hlt }
          omega
        have left_x := lt_lemma idx i (by omega) (by omega) (by omega)
        have right_x := lt_lemma i (idx + 1) (by omega) (by omega) (by omega)
        omega }
      simp at ex
      simp [getValSpV_empty spv pos ex]
    rcases (em ((SpVT.ind spv1)[p1 + 1] ≤ x)) with c1 | c2
    { simp [c1] at val
      simp [interm_lemma spv2 x p2 (by omega) (by omega)] }
    simp at c2
    simp [interm_lemma spv1 x p1 (by omega) (by omega)]
  | case3 p1 p2 h1 neq le ih =>
    rw [spv_dot, if_neg h1, if_neg neq, if_pos le, ih]
    apply Finset.sum_congr
    { rfl }
    intro x hx
    by_cases edg: SpVT.size spv1 = p1 + 1
    { have sz_concl := sz1 p1 (by omega)
      simp [edg]
      simp at hx
      have nx : ¬(n ≤ x) := by omega
      by_cases b2: SpVT.size spv2 ≤ p2 <;> simp [b2] <;> simp [nx]
      by_cases ifc: (SpVT.ind spv1)[p1] ≤ x ∧ (SpVT.ind spv2)[p2] ≤ x <;> simp [ifc]
      by_cases ex: ∃ i < SpVT.size spv1, (SpVT.ind spv1)[i] = x
      { rcases ex with ⟨i, ib, hi⟩
        by_cases il: p1 < i
        { omega }
        simp at il
        rcases (le_iff_eq_or_lt.mp il) with ieq | ilt
        { simp [ieq] at hi
          omega }
        have contra := SpVT.h_inc spv1 i p1 ib (by omega) ilt
        simp [getElem] at hi
        simp [getElem] at ifc
        omega }
      simp at ex
      simp [getValSpV_empty spv1 x ex] }
    have inb: ¬(SpVT.size spv1 ≤ p1 + 1) ∧ ¬(SpVT.size spv1 ≤ p1):= by omega
    simp [inb]
    by_cases edg2: SpVT.size spv2 ≤ p2 <;> simp [edg2]
    { simp at hx
      have neg: ¬ (n ≤ x) := by omega
      simp [neg] }
    by_cases le2: (SpVT.ind spv2)[p2] ≤ x <;> simp [le2]
    by_cases upper: (SpVT.ind spv1)[p1 + 1] ≤ x <;> simp [upper]
    { simp at inb
      simp [getElem]
      simp [le_trans (le_of_lt (SpVT.h_inc spv1 p1 (p1 + 1) inb.right inb.left (by simp))) upper] }
    by_cases lower: (SpVT.ind spv1)[p1] ≤ x <;> simp [lower]
    by_cases ex: ∃ i < SpVT.size spv1, (SpVT.ind spv1)[i] = x
    { rcases ex with ⟨ind, indb, hind⟩
      by_cases ind_x: ind = p1
      { simp [ind_x] at hind
        omega }
      rcases (lt_or_gt_of_ne ind_x) with ltc | gtc
      { have contra := SpVT.h_inc spv1 ind p1 indb (by omega) ltc
        simp [getElem] at lower
        simp [getElem] at hind
        omega }
      by_cases indp1: ind = p1 + 1
      { simp [indp1] at hind
        omega }
      have indlt: p1 + 1 < ind := by omega
      have contra := SpVT.h_inc spv1 (p1 + 1) ind (by omega) indb indlt
      simp [getElem] at upper
      simp [getElem] at hind
      omega }
    simp at ex
    simp [getValSpV_empty spv1 x ex]
  | case4 p1 p2 h1 neq nle ih =>
    rw [spv_dot, if_neg h1, if_neg neq, if_neg nle, ih]
    apply Finset.sum_congr
    { rfl }
    intro x hx
    by_cases edg: SpVT.size spv2 = p2 + 1
    { have sz_concl := sz2 p2 (by omega)
      simp [edg]
      simp at hx
      have nx : ¬(n ≤ x) := by omega
      by_cases b1: SpVT.size spv1 ≤ p1 <;> simp [b1] <;> simp [nx]
      by_cases ifc: (SpVT.ind spv1)[p1] ≤ x ∧ (SpVT.ind spv2)[p2] ≤ x <;> simp [ifc]
      by_cases ex: ∃ i < SpVT.size spv2, (SpVT.ind spv2)[i] = x
      { rcases ex with ⟨i, ib, hi⟩
        by_cases il: p2 < i
        { omega }
        simp at il
        rcases (le_iff_eq_or_lt.mp il) with ieq | ilt
        { simp [ieq] at hi
          omega }
        have contra := (SpVT.h_inc spv2) i p2 ib (by omega) ilt
        simp [getElem] at hi
        simp [getElem] at ifc
        omega }
      simp at ex
      simp [getValSpV_empty spv2 x ex] }
    have inb: ¬(SpVT.size spv2 ≤ p2 + 1) ∧ ¬(SpVT.size spv2 ≤ p2):= by omega
    simp [inb]
    by_cases edg1: SpVT.size spv1 ≤ p1 <;> simp [edg1]
    { simp at hx
      have neg: ¬ (n ≤ x) := by omega
      simp [neg] }
    by_cases le1: (SpVT.ind spv1)[p1] ≤ x <;> simp [le1]
    by_cases upper: (SpVT.ind spv2)[p2 + 1] ≤ x <;> simp [upper]
    { simp at inb
      simp [getElem]
      simp [le_trans (le_of_lt ((SpVT.h_inc spv2) p2 (p2 + 1) inb.right inb.left (by simp))) upper] }
    by_cases lower: (SpVT.ind spv2)[p2] ≤ x <;> simp [lower]
    by_cases ex: ∃ i < SpVT.size spv2, (SpVT.ind spv2)[i] = x
    { rcases ex with ⟨ind, indb, hind⟩
      by_cases ind_x: ind = p2
      { simp [ind_x] at hind
        omega }
      rcases (lt_or_gt_of_ne ind_x) with ltc | gtc
      { have contra := (SpVT.h_inc spv2) ind p2 indb (by omega) ltc
        simp [getElem] at lower
        simp [getElem] at hind
        omega }
      by_cases indp2: ind = p2 + 1
      { simp [indp2] at hind
        omega }
      have indlt: p2 + 1 < ind := by omega
      have contra := (SpVT.h_inc spv2) (p2 + 1) ind (by omega) indb indlt
      simp [getElem] at upper
      simp [getElem] at hind
      omega }
    simp at ex
    simp [getValSpV_empty spv2 x ex]

theorem spv_dot_pure (spv1 spv2: SpVAbs) (n: ℕ)
  (sz1: ∀ i < SpVT.size spv1, (SpVT.ind spv1)[i] < n) (sz2: ∀ i < SpVT.size spv2, (SpVT.ind spv2)[i] < n):
    spv_dot spv1 spv2 0 0 = ∑ i ∈ Finset.range n, spv1[i] * spv2[i] := by
      simp [spv_dot_pure_gen spv1 spv2 n 0 0 sz1 sz2]
      apply Finset.sum_congr
      { rfl }
      intro x hx
      simp at hx
      by_cases em1: SpVT.size spv1 = 0 <;> simp [em1]
      { simp [lt_iff_le_not_le.mp hx]
        simp [getValSpV_empty spv1 x (by intro i hi; omega)] }
      by_cases em2: SpVT.size spv2 = 0 <;> simp [em2]
      { intros
        simp [getValSpV_empty spv2 x (by intro i hi; omega)] }
      intro zer_ineq
      have zer_lemma (spv: SpVAbs) (i: ℕ) (hsz: SpVT.size spv ≠ 0): i < (SpVT.ind spv)[0] → spv[i] = 0 := by
        intro lt
        have all_none: ∀ j < SpVT.size spv, (SpVT.ind spv)[j] ≠ i := by
          intro i1 hi1
          by_cases i10 : i1 = 0
          { simp [←i10] at lt
            omega }
          have contra := SpVT.h_inc spv  0 i1 (by omega) (by omega) (by omega)
          simp [getElem]
          simp [getElem] at lt
          omega
        simp [getValSpV_empty spv i all_none]
      by_cases sm1: (SpVT.ind spv1)[0] ≤ x
      { simp [sm1] at zer_ineq
        simp [zer_lemma spv2 x em2 zer_ineq] }
      simp at sm1
      simp [zer_lemma spv1 x em1 sm1]

method SpVSpV
  (mut out: arrVal)
  (spv1: SpVAbs)
  (spv2: SpVAbs) return (u: Unit)
  ensures size outNew = 1
  ensures outNew[0] = spv_dot spv1 spv2 0 0
  do
    out := val_inst.replicate 1 0
    let mut pnt1 := 0
    let mut pnt2 := 0
    while pnt1 ≠ SpVT.size spv1 ∧ pnt2 ≠ SpVT.size spv2
    invariant size out = 1
    invariant pnt1 ≤ SpVT.size spv1 ∧ pnt2 ≤ SpVT.size spv2
    invariant out[0] + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0
    done_with pnt1 = SpVT.size spv1 ∨ pnt2 = SpVT.size spv2
    do
      if (SpVT.ind spv1)[pnt1] = (SpVT.ind spv2)[pnt2] then
        out[0] += (SpVT.val spv1)[pnt1] * (SpVT.val spv2)[pnt2]
        pnt1 := pnt1 + 1
        pnt2 := pnt2 + 1
      else
        if (SpVT.ind spv1)[pnt1] < (SpVT.ind spv2)[pnt2] then
          pnt1 := pnt1 + 1
        else
          pnt2 := pnt2 + 1
    return

prove_correct SpVSpV by
  dsimp [SpVSpV]
  velvet_solve

theorem SpVSpV_correct_triple (out: arrVal) (spv1 spv2: SpVAbs) (n: ℕ):
  triple
    ((∀ i < SpVT.size spv1, (SpVT.ind spv1)[i] < n) ∧ (∀ i < SpVT.size spv2, (SpVT.ind spv2)[i] < n))
    (SpVSpV out spv1 spv2)
    fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
      outNew[0] = ∑ i ∈ Finset.range n, spv1[i] * spv2[i] := by
      simp [triple]
      intro b1 b2
      apply wp_cons (SpVSpV out spv1 spv2)
        fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
          outNew[0] = spv_dot spv1 spv2 0 0 ∧ size outNew = 1
      { rintro ⟨_, ⟨outNew, PUnit.unit⟩⟩; simp
        intro sum_eq sz_eq
        simp [sum_eq]
        exact spv_dot_pure spv1 spv2 n b1 b2 }
      simp
      have triple_true := SpVSpV_correct out spv1 spv2
      simp [triple] at triple_true
      simp [WithName] at triple_true
      exact triple_true

method SpMSpV
  (mut out: arrVal)
  (spm: arrSpV)
  (spv: SpVAbs) return (u: Unit)
  ensures size outNew = size spm
  ensures ∀ i < size spm, outNew[i] = spv_dot spm[i] spv 0 0
  do
    out := val_inst.replicate (size spm) 0
    let mut spmInd := ind_inst.replicate (size spm) 0
    let mut spvInd := ind_inst.replicate (size spm) 0
    while_some i :| i < (size spm) ∧ TArray.get i spmInd < SpVT.size (TArray.get i spm) ∧ TArray.get i spvInd < SpVT.size spv
    invariant ind_inst.size spvInd = size spm
    invariant ind_inst.size spmInd = size spm
    invariant size out = size spm
    invariant ∀ i < ind_inst.size spmInd, spmInd[i] <= SpVT.size spm[i]
    invariant ∀ i < ind_inst.size spvInd, spvInd[i] <= SpVT.size spv
    invariant ∀ i < size spm, out[i] + spv_dot spm[i] spv spmInd[i] spvInd[i] = spv_dot spm[i] spv 0 0
    done_with ∀ i < size spm, spmInd[i] = SpVT.size spm[i] ∨ spvInd[i] = SpVT.size spv
    do
      let ind_m := spmInd[i]
      let ind_v := spvInd[i]
      if TArray.get ind_m (SpVT.ind spm[i]) = TArray.get ind_v (SpVT.ind spv) then
        out[i] += TArray.get ind_m (SpVT.val spm[i]) * TArray.get ind_v (SpVT.val spv)
        spmInd[i] += 1
        spvInd[i] += 1
      else
        if (SpVT.ind spm[i])[ind_m] < (SpVT.ind spv)[ind_v] then
          spmInd[i] += 1
        else
          spvInd[i] += 1
    return
prove_correct SpMSpV by
  dsimp [SpMSpV]
  velvet_solve


theorem SpMSpV_correct_triple
  (out: arrVal)
  (spm: arrSpV)
  (spv: SpVAbs)
  (n: ℕ):
  triple
    (∀ i < size spm, (∀ j < SpVT.size (TArray.get i spm), (SpVT.ind (TArray.get i spm))[j] < n) ∧ (∀ j < SpVT.size spv, (SpVT.ind spv)[j] < n))
    (SpMSpV out spm spv)
    fun ⟨_, ⟨outNew, _⟩⟩ =>
      size outNew = size spm ∧ ∀ i < size spm, outNew[i] = ∑ idx ∈ Finset.range n, (TArray.get i spm)[idx] * spv[idx] := by
        simp [triple]
        intro inb
        apply wp_cons (SpMSpV out spm spv)
          fun ⟨_, ⟨outNew, _⟩⟩ =>
            (∀ i < size spm, outNew[i] = spv_dot (TArray.get i spm) spv 0 0) ∧ size outNew = size spm
        { rintro ⟨_, ⟨outNew, _⟩⟩; simp
          intro sum_eq sz_eq
          simp [sz_eq]
          intro i ib
          simp [←spv_dot_pure (TArray.get i spm) spv n (inb i ib).left (inb i ib).right]
          exact sum_eq i ib }
        simp
        have triple_true := SpMSpV_correct out spm spv
        simp [triple] at triple_true
        simp [WithName] at triple_true
        exact triple_true

end SpMV
