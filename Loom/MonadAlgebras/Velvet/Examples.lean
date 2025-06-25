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

open PartialCorrectness DemonicChoice

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

class TArray (α : outParam Type) (κ: Type) where
  get : Nat → κ → α
  set : Nat → α → κ → κ
  size : κ → Nat
  get_set (idx₁ idx₂ val arr) : idx₁ < size arr -> get idx₁ (set idx₂ val arr) =
      if idx₁ = idx₂ then val else get idx₁ arr
  size_set (idx val arr) : size (set idx val arr) = size arr

  replicate : Nat → α → κ
  replicate_size (sz elem): size (replicate sz elem) = sz
  replicate_get (sz elem) (i : Nat) (h_i : i < sz) : get i (replicate sz elem) = elem

  toMultiset : κ -> Multiset α
  multiSet_swap (arr : κ) (idx₁ idx₂) :
    idx₁ < size arr ->
    idx₂ < size arr ->
    toMultiset (set idx₁ (get idx₂ arr) (set idx₂ (get idx₁ arr) arr)) =
    toMultiset arr


instance [Inhabited α] : TArray α (Array α) where
  get i arr := arr[i]!
  set i val arr := arr.set! i val
  size arr := arr.size
  get_set i j val arr := by
    intro h
    by_cases h' : j < arr.size
    { simp [Array.setIfInBounds, dif_pos h']
      rw [getElem!_pos, getElem!_pos] <;> try simp [*]
      rw [@Array.getElem_set]; aesop }
    simp [Array.setIfInBounds, dif_neg h']
    rw [getElem!_pos] <;> try simp [*]
    split_ifs; omega; rfl
  size_set i val arr := by simp
  replicate sz elem := Array.replicate sz elem
  replicate_size sz elem := by simp
  replicate_get sz elem i h_i := by rw [getElem!_pos] <;> try simp [*]
  toMultiset arr := Multiset.ofList arr.toList
  multiSet_swap arr idx₁ idx₂ h_idx₁ h_idx₂ := by classical
    simp [List.perm_iff_count]
    intro a;
    rw [getElem!_pos,getElem!_pos] <;> try simp [*]
    rw [List.count_set] <;> try simp [*]
    rw [List.count_set] <;> try simp [*]
    simp [List.getElem_set]
    split_ifs with h <;> try simp
    have : Array.count a arr > 0 := by
      apply Array.count_pos_iff.mpr; simp [<-h]
    omega

attribute [solverHint] TArray.get_set TArray.size_set

export TArray (get set size toMultiset)

instance [TArray α κ] : GetElem κ Nat α fun _ _ => True where
  getElem inst i _ := TArray.get i inst

instance [Inhabited α] [TArray α κ] : Inhabited κ where
  default := TArray.replicate 0 default

@[loomAbstractionSimp]
lemma getElemE (α κ) {_ : TArray α κ} (k : κ) : k[i] = get i k := by
  rfl

syntax (priority := high + 1) ident noWs "[" term "]" ":=" term : doElem
syntax (priority := high + 1) ident noWs "[" term "]" "+=" term : doElem

macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := TArray.set $idx $val $id:term)
  | `(doElem|$id:ident[$idx:term] += $val:term) =>
    `(doElem| $id:term := TArray.set $idx (($id:term)[$idx] + $val) $id:term)


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

set_option trace.profiler true in
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
  correct_by by {
    dsimp [spmv]
    velvet_solve
  }

/-
def toList [arr_inst: TArray ε τ] (arr: τ): List ε :=
  (List.range (arr_inst.size arr)).map (fun i => arr_inst.get i arr)

instance [Inhabited β] [AddCommMonoid β] [v_inst: TArray β σ] [i_inst: TArray Nat μ] : GetElem (SpV β μ σ) ℕ β fun _ _ => True where
  getElem inst i _ :=
    match (List.zip (toList inst.ind) (toList inst.val)).find? fun (j, _) => j = i with
    | some pr => pr.2
    | none => 0

method VSpV
  (mut out: Array α)
  (arr: κ)
  (spv: SpV α κ γ) return (u: Unit)
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
  correct_by by { simp [VSpV]; cannon }

theorem getValSpV_eq (spv: SpV α κ γ) (j: ℕ) (h_ind: j < spv.size): spv[spv.ind[j]] = spv.val[j] := by
  simp [getElem]
  have just_case: List.find? (fun x ↦ decide (x.1 = spv.ind[j])) (List.zip (toList spv.ind) (toList spv.val)) = some ((spv.ind[j], spv.val[j])):= by
    apply List.find?_eq_some_iff_getElem.mpr
    simp
    exists j
    rw [←spv.h_sz_eq.left] at h_ind
    constructor
    { simp [toList]
      simp [GetElem.getElem]
      rintro j₁ j₁_lt
      rw [spv.h_sz_eq.left] at h_ind
      have inj := spv.h_inc j₁ j (lt_trans j₁_lt h_ind) h_ind j₁_lt
      simp [GetElem.getElem] at inj
      simp [lt_iff_le_and_ne.mp inj] }
    simp [toList, h_ind]; rw [spv.h_sz_eq.right, ←spv.h_sz_eq.left]; simp [h_ind]
  simp [GetElem.getElem] at just_case
  simp [just_case]

theorem getValSpV_empty (spv: SpV α κ γ) (j: ℕ) (h_empty: ∀ i < spv.size, spv.ind[i] ≠ j): spv[j] = 0 := by
  simp [getElem]
  have none_case: List.find? (fun x ↦ decide (x.1 = j)) (List.zip (toList spv.ind) (toList spv.val)) = none := by
    apply List.find?_eq_none.mpr
    rintro x x_in; simp
    have zip_part := List.of_mem_zip x_in
    simp [List.mem_iff_get] at zip_part
    rcases zip_part.left with ⟨i, hi⟩
    have neq := h_empty i (have ilt := i.isLt; by simp [toList, spv.h_sz_eq.left] at ilt; simp [ilt])
    simp [toList] at hi
    simp [GetElem.getElem] at neq
    simp [hi] at neq
    simp [neq]
  simp [none_case]

theorem VSpV_correct_pure (out: Array α) (arr: κ)
  (spv: SpV α κ γ)
  (h_b: ∀ i < spv.size, spv.ind[i] < ind_inst.size arr):
  out.size = 1 → out[0]! = spv.sumUpTo (fun _ ind v => v * arr[ind]) spv.size →
    out[0]! = ∑ i ∈ Finset.range (ind_inst.size arr), spv[i] * arr[i] := by
      intro sz sum_eq
      rw [sum_eq, SpV.sumUpTo]
      have ind_lemma: ∀ k, k ≤ ind_inst.size arr →
        ∑ i ∈ Finset.range spv.size, (if spv.ind[i] < k then spv.val[i] * arr[spv.ind[i]] else 0) =
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
              (∑ i ∈ Finset.range (ind_inst.size spv.ind), if spv.ind[i] < m then spv.val[i] * arr[spv.ind[i]] else 0) +
              (∑ i ∈ Finset.range (ind_inst.size spv.ind), if spv.ind[i] = m then spv.val[i] * arr[spv.ind[i]] else 0) =
              (∑ i ∈ Finset.range (ind_inst.size spv.ind), if spv.ind[i] < m + 1 then spv.val[i] * arr[spv.ind[i]] else 0) := by
                rw [←Finset.sum_add_distrib]
                rw [Finset.sum_congr (by rfl)]
                intro x hx
                by_cases h_eq_m : spv.ind[x] = m <;> simp [h_eq_m]
                have miff : spv.ind[x] < m ↔ spv.ind[x] < m + 1 := by
                  constructor <;> rintro h_lt <;> omega
                simp [miff]
            rw [←spv.h_sz_eq.left, ←splitted_sum, add_left_cancel_iff.mpr]
            by_cases exists_i: ∃ i < spv.size, spv.ind[i] = m
            { rcases exists_i with ⟨ind, h_ind⟩
              rw [← h_ind.right]
              have lemma_res := getValSpV_eq spv ind h_ind.left
              simp at lemma_res
              simp [lemma_res]
              have almost_zero : ∀ i ∈ Finset.range (ind_inst.size spv.ind), i ≠ ind →
                ((if spv.ind[i] = spv.ind[ind] then spv.val[i] * arr[spv.ind[i]] else 0) = 0) := by
                  intro i i_inb i_not_ind
                  by_cases vind_eq : spv.ind[i] = spv.ind[ind]
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
                ((if spv.ind[ind] = spv.ind[ind] then spv.val[ind] * arr[spv.ind[ind]] else 0) = 0) := by
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
            by_cases h_eq: spv.ind[x] = m <;> simp [h_eq]
            simp [←h_eq] at h_getVal
            simp at hx
            rw [spv.h_sz_eq.left] at hx
            simp [getValSpV_eq spv x hx] at h_getVal
            simp [h_getVal]
      have fin_lemma := ind_lemma (ind_inst.size arr) (by rfl)
      rw [←fin_lemma]
      exact Finset.sum_congr (by rfl) fun i h_i => by aesop

theorem VSpV_correct_triple (out: Array α) (arr: κ) (spv: SpV α κ γ):
  triple
    (∀ i < spv.size, spv.ind[i]! < ind_inst.size arr)
    (VSpV out arr spv)
    fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
      outNew[0]! = ∑ i ∈ Finset.range (ind_inst.size arr), spv[i] * arr[i]! := by
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

theorem spmv_correct_triple (out: Array α) (arr: κ) (spm: Array (SpV α κ γ)):
  triple
    (∀ i < spm.size, ∀ j < spm[i]!.size, spm[i]!.ind[j] < ind_inst.size arr)
    (spmv out arr spm)
    fun ⟨_, ⟨outNew, _⟩⟩ =>
      (∀ j < outNew.size, outNew[j]! = ∑ i ∈ Finset.range (ind_inst.size arr), spm[j]![i] * arr[i]) := by
      simp [triple]
      intro h_b
      apply wp_cons
        (spmv out arr spm)
        fun ⟨_, ⟨outNew, _⟩⟩ =>
          ((spm.size = outNew.size) ∧ ∀ i < spm.size, outNew[i]! = spm[i]!.sumUpTo (fun _ ind v => v * arr[ind]) spm[i]!.size)
      { simp; rintro ⟨_, ⟨outNew⟩⟩; simp
        intro sz_eq sum_eq j h_j
        have single_elem : #[outNew[j]!][0] = outNew[j]! := by simp
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

set_option maxHeartbeats 5000000

def spv_dot (spv1 spv2: SpV α κ γ) (pnt1 pnt2: ℕ): α :=
  if spv1.size ≤ pnt1 ∨ spv2.size ≤ pnt2 then
    0
  else
    if spv1.ind[pnt1] = spv2.ind[pnt2] then
      spv1.val[pnt1] * spv2.val[pnt2] + spv_dot spv1 spv2 (pnt1 + 1) (pnt2 + 1)
    else
      if spv1.ind[pnt1] < spv2.ind[pnt2] then
        spv_dot spv1 spv2 (pnt1 + 1) pnt2
      else
        spv_dot spv1 spv2 pnt1 (pnt2 + 1)
  termination_by (spv1.size + spv2.size - pnt1 - pnt2)

@[simp]
theorem spv_dot_eq (spv1 spv2: SpV α κ γ) (pnt1 pnt2: ℕ) (prev: α):
  prev + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0 → spv1.ind[pnt1] = spv2.ind[pnt2] →
  pnt1 ≤ spv1.size → ¬(pnt1 = spv1.size) → pnt2 ≤ spv2.size → ¬(pnt2 = spv2.size) →
    prev + spv1.val[pnt1] * spv2.val[pnt2] + spv_dot spv1 spv2 (pnt1 + 1) (pnt2 + 1) = spv_dot spv1 spv2 0 0 := by
      intro sum_eq ind_eq inb1 neq1 inb2 neq2
      rw [spv_dot] at sum_eq
      have neq: ¬(spv1.size ≤ pnt1 ∨ spv2.size ≤ pnt2) := by omega
      simp [neq, ind_eq] at sum_eq
      rw [←add_assoc] at sum_eq
      exact sum_eq


@[simp]
theorem spv_dot_lt (spv1 spv2: SpV α κ γ) (pnt1 pnt2: ℕ) (prev: α):
  prev + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0 → spv1.ind[pnt1] < spv2.ind[pnt2] →
  pnt1 ≤ spv1.size → ¬(pnt1 = spv1.size) → pnt2 ≤ spv2.size → ¬(pnt2 = spv2.size) →
    prev + spv_dot spv1 spv2 (pnt1 + 1) pnt2 = spv_dot spv1 spv2 0 0 := by
      intro sum_eq ind_lt inb1 neq1 inb2 neq2
      rw [spv_dot] at sum_eq
      have neq: ¬(spv1.size ≤ pnt1 ∨ spv2.size ≤ pnt2) := by omega
      simp [neq, ind_lt] at sum_eq
      simp [lt_iff_le_and_ne.mp ind_lt] at sum_eq
      exact sum_eq


@[simp]
theorem spv_dot_gt (spv1 spv2: SpV α κ γ) (pnt1 pnt2: ℕ) (prev: α):
  prev + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0 → spv2.ind[pnt2] ≤ spv1.ind[pnt1] → spv1.ind[pnt1] ≠ spv2.ind[pnt2] →
  pnt1 ≤ spv1.size → ¬(pnt1 = spv1.size) → pnt2 ≤ spv2.size → ¬(pnt2 = spv2.size) →
    prev + spv_dot spv1 spv2 pnt1 (pnt2 + 1) = spv_dot spv1 spv2 0 0 := by
      intro sum_eq ind_le ind_neq inb1 neq1 inb2 neq2
      rw [spv_dot] at sum_eq
      have neq: ¬(spv1.size ≤ pnt1 ∨ spv2.size ≤ pnt2) := by omega
      simp [neq, ind_neq, ind_le] at sum_eq
      have ilt: ¬(spv1.ind[pnt1] < spv2.ind[pnt2]) := by omega
      simp [ilt] at sum_eq
      exact sum_eq


--in fact, this is only needed for aesop to use lemmas above
@[simp]
theorem lt_ne_le {a b: Nat} (h: a < b): a ≤ b ∧ ¬(a = b) := Nat.lt_iff_le_and_ne.mp h

@[simp]
theorem spv_dot_exh (spv1 spv2: SpV α κ γ) (pnt1 pnt2: ℕ):
  pnt1 = spv1.size ∨ pnt2 = spv2.size → spv_dot spv1 spv2 pnt1 pnt2 = 0 := by
    intro exh
    rw [spv_dot]
    by_cases triv: spv1.size ≤ pnt1 ∨ spv2.size ≤ pnt2 <;> simp [triv]
    omega

theorem spv_dot_pure_gen (spv1 spv2: SpV α κ γ) (n pnt1 pnt2: ℕ)
  (sz1: ∀ i < spv1.size, spv1.ind[i] < n)
  (sz2: ∀ i < spv2.size, spv2.ind[i] < n):
  spv_dot spv1 spv2 pnt1 pnt2 =
    ∑ i ∈ Finset.range n,
      if max
        (if spv1.size ≤ pnt1 then n else spv1.ind[pnt1])
        (if spv2.size ≤ pnt2 then n else spv2.ind[pnt2]) ≤ i then
        spv1[i] * spv2[i]
      else
        0 := by
  fun_induction spv_dot spv1 spv2 pnt1 pnt2 with
  | case1 p1 p2 h =>
    rw [spv_dot]
    rw [if_pos h]
    have all_zero: (∀ x ∈ Finset.range n, (if max (if spv1.size ≤ p1 then n else spv1.ind[p1]) (if spv2.size ≤ p2 then n else spv2.ind[p2]) ≤ x then spv1[x] * spv2[x] else 0) = 0) := by
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
      ∑ i ∈ Finset.range n, (if i = spv1.ind[p1] then spv1[spv1.ind[p1]] * spv2[spv1.ind[p1]] else 0) = (if spv1.ind[p1] = spv1.ind[p1] then spv1[spv1.ind[p1]] * spv2[spv1.ind[p1]] else 0) := by
      have hb: ∀ i ∈ Finset.range n, i ≠ spv1.ind[p1] → ((if i = spv1.ind[p1] then spv1[spv1.ind[p1]] * spv2[spv1.ind[p1]] else 0) = 0) := by
        intro i hi iq
        simp at hi
        simp [iq]
      have hc: spv1.ind[p1] ∉ Finset.range n → ((if spv1.ind[p1] = spv1.ind[p1] then spv1[spv1.ind[p1]] * spv2[spv1.ind[p1]] else 0) = 0) := by
        intro nin
        simp at nin
        have bnd := sz1 p1 (by omega)
        omega
      apply Finset.sum_eq_single spv1.ind[p1] hb hc
    simp at sum_eq_single
    rw [←eq, ←sum_eq_single]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr
    { rfl }
    intro x hx
    simp at hx
    have h2: ¬spv1.size ≤ p1 ∧ ¬spv2.size ≤ p2 := by omega
    simp [h2]
    have hnx: ¬(n ≤ x) := by simp [hx]
    by_cases xeq: x = spv1.ind[p1] <;> simp [xeq]
    { intro in1 in2
      by_cases edg1: spv1.size ≤ p1 + 1 <;> simp [edg1] at in1
      { omega }
      have p1lt := spv1.h_inc p1 (p1 + 1) (by omega) (by omega) (by simp)
      omega }
    have outb_lemma (spv: SpV α κ γ) (pos: ℕ) (hsz: 1 ≤ spv.size) (hb: spv.ind[spv.size - 1] < pos): spv[pos] = 0 := by
      by_cases ex: ∃ i < spv.size, spv.ind[i] = pos
      { rcases ex with ⟨i, hbi, hi⟩
        by_cases heq: i = spv.size - 1
        { simp [heq] at hi
          omega }
        have contra := spv.h_inc i (spv.size - 1) (by omega) (by omega) (by omega)
        omega }
      simp at ex
      simp [getValSpV_empty spv pos ex]
    by_cases edg1: spv1.size ≤ p1 + 1 <;> simp [edg1]
    { simp [hnx]
      have p1eq : p1 = spv1.size - 1 := by omega
      by_cases lex: spv1.ind[p1] ≤ x <;> simp [lex]
      have ltx: spv1.ind[p1] < x := by omega
      simp [p1eq] at ltx
      simp [outb_lemma spv1 x (by omega) ltx] }
    by_cases edg2: spv2.size ≤ p2 + 1 <;> simp [edg2]
    { simp [hnx]
      by_cases lex: spv1.ind[p1] ≤ x <;> simp [lex]
      have ltx: spv1.ind[p1] < x := by omega
      have p2eq: p2 = spv2.size - 1 := by omega
      simp [eq, p2eq] at ltx
      simp [outb_lemma spv2 x (by omega) ltx] }
    by_cases val: spv1.ind[p1 + 1] ≤ x ∧ spv2.ind[p2 + 1] ≤ x <;> simp [val]
    { have inc: spv1.ind[p1] < spv1.ind[p1 + 1] := spv1.h_inc p1 (p1 + 1) (by omega) (by omega) (by simp)
      simp [le_of_lt (lt_of_lt_of_le inc val.left)] }
    by_cases xb: spv1.ind[p1] ≤ x <;> simp [xb]
    have ltx: spv1.ind[p1] < x := by omega
    simp at val
    have interm_lemma (spv: SpV α κ γ) (pos idx: ℕ) (hsz: idx + 1 < spv.size) (inter: spv.ind[idx] < pos ∧ pos < spv.ind[idx + 1]): spv[pos] = 0 := by
      by_cases ex: ∃ i < spv.size, spv.ind[i] = pos
      { rcases ex with ⟨i, hbi, hi⟩
        have lt_lemma (i1 i2: ℕ) (hi1: i1 < spv.size) (hi2: i2 < spv.size): spv.ind[i1] < spv.ind[i2] → i1 < i2 := by
          intro hlt
          by_cases contra_lt: i2 < i1
          { have inc := spv.h_inc i2 i1 hi2 hi1 contra_lt
            omega }
          by_cases contra_eq: i1 = i2
          { simp [contra_eq] at hlt }
          omega
        have left_x := lt_lemma idx i (by omega) (by omega) (by omega)
        have right_x := lt_lemma i (idx + 1) (by omega) (by omega) (by omega)
        omega }
      simp at ex
      simp [getValSpV_empty spv pos ex]
    rcases (em (spv1.ind[p1 + 1] ≤ x)) with c1 | c2
    { simp [c1] at val
      simp [interm_lemma spv2 x p2 (by omega) (by omega)] }
    simp at c2
    simp [interm_lemma spv1 x p1 (by omega) (by omega)]
  | case3 p1 p2 h1 neq le ih =>
    rw [spv_dot, if_neg h1, if_neg neq, if_pos le, ih]
    apply Finset.sum_congr
    { rfl }
    intro x hx
    by_cases edg: spv1.size = p1 + 1
    { have sz_concl := sz1 p1 (by omega)
      simp [edg]
      simp at hx
      have nx : ¬(n ≤ x) := by omega
      by_cases b2: spv2.size ≤ p2 <;> simp [b2] <;> simp [nx]
      by_cases ifc: spv1.ind[p1] ≤ x ∧ spv2.ind[p2] ≤ x <;> simp [ifc]
      by_cases ex: ∃ i < spv1.size, spv1.ind[i] = x
      { rcases ex with ⟨i, ib, hi⟩
        by_cases il: p1 < i
        { omega }
        simp at il
        rcases (le_iff_eq_or_lt.mp il) with ieq | ilt
        { simp [ieq] at hi
          omega }
        have contra := spv1.h_inc i p1 ib (by omega) ilt
        omega }
      simp at ex
      simp [getValSpV_empty spv1 x ex] }
    have inb: ¬(spv1.size ≤ p1 + 1) ∧ ¬(spv1.size ≤ p1):= by omega
    simp [inb]
    by_cases edg2: spv2.size ≤ p2 <;> simp [edg2]
    { simp at hx
      have neg: ¬ (n ≤ x) := by omega
      simp [neg] }
    by_cases le2: spv2.ind[p2] ≤ x <;> simp [le2]
    by_cases upper: spv1.ind[p1 + 1] ≤ x <;> simp [upper]
    { simp at inb
      simp [le_trans (le_of_lt (spv1.h_inc p1 (p1 + 1) inb.right inb.left (by simp))) upper] }
    by_cases lower: spv1.ind[p1] ≤ x <;> simp [lower]
    by_cases ex: ∃ i < spv1.size, spv1.ind[i] = x
    { rcases ex with ⟨ind, indb, hind⟩
      by_cases ind_x: ind = p1
      { simp [ind_x] at hind
        omega }
      rcases (lt_or_gt_of_ne ind_x) with ltc | gtc
      { have contra := spv1.h_inc ind p1 indb (by omega) ltc
        omega }
      by_cases indp1: ind = p1 + 1
      { simp [indp1] at hind
        omega }
      have indlt: p1 + 1 < ind := by omega
      have contra := spv1.h_inc (p1 + 1) ind (by omega) indb indlt
      omega }
    simp at ex
    simp [getValSpV_empty spv1 x ex]
  | case4 p1 p2 h1 neq nle ih =>
    rw [spv_dot, if_neg h1, if_neg neq, if_neg nle, ih]
    apply Finset.sum_congr
    { rfl }
    intro x hx
    by_cases edg: spv2.size = p2 + 1
    { have sz_concl := sz2 p2 (by omega)
      simp [edg]
      simp at hx
      have nx : ¬(n ≤ x) := by omega
      by_cases b1: spv1.size ≤ p1 <;> simp [b1] <;> simp [nx]
      by_cases ifc: spv1.ind[p1] ≤ x ∧ spv2.ind[p2] ≤ x <;> simp [ifc]
      by_cases ex: ∃ i < spv2.size, spv2.ind[i] = x
      { rcases ex with ⟨i, ib, hi⟩
        by_cases il: p2 < i
        { omega }
        simp at il
        rcases (le_iff_eq_or_lt.mp il) with ieq | ilt
        { simp [ieq] at hi
          omega }
        have contra := spv2.h_inc i p2 ib (by omega) ilt
        omega }
      simp at ex
      simp [getValSpV_empty spv2 x ex] }
    have inb: ¬(spv2.size ≤ p2 + 1) ∧ ¬(spv2.size ≤ p2):= by omega
    simp [inb]
    by_cases edg1: spv1.size ≤ p1 <;> simp [edg1]
    { simp at hx
      have neg: ¬ (n ≤ x) := by omega
      simp [neg] }
    by_cases le1: spv1.ind[p1] ≤ x <;> simp [le1]
    by_cases upper: spv2.ind[p2 + 1] ≤ x <;> simp [upper]
    { simp at inb
      simp [le_trans (le_of_lt (spv2.h_inc p2 (p2 + 1) inb.right inb.left (by simp))) upper] }
    by_cases lower: spv2.ind[p2] ≤ x <;> simp [lower]
    by_cases ex: ∃ i < spv2.size, spv2.ind[i] = x
    { rcases ex with ⟨ind, indb, hind⟩
      by_cases ind_x: ind = p2
      { simp [ind_x] at hind
        omega }
      rcases (lt_or_gt_of_ne ind_x) with ltc | gtc
      { have contra := spv2.h_inc ind p2 indb (by omega) ltc
        omega }
      by_cases indp2: ind = p2 + 1
      { simp [indp2] at hind
        omega }
      have indlt: p2 + 1 < ind := by omega
      have contra := spv2.h_inc (p2 + 1) ind (by omega) indb indlt
      omega }
    simp at ex
    simp [getValSpV_empty spv2 x ex]

theorem spv_dot_pure (spv1 spv2: SpV α κ γ) (n: ℕ)
  (sz1: ∀ i < spv1.size, spv1.ind[i] < n) (sz2: ∀ i < spv2.size, spv2.ind[i] < n):
    spv_dot spv1 spv2 0 0 = ∑ i ∈ Finset.range n, spv1[i] * spv2[i] := by
      simp [spv_dot_pure_gen spv1 spv2 n 0 0 sz1 sz2]
      apply Finset.sum_congr
      { rfl }
      intro x hx
      simp at hx
      by_cases em1: spv1.size = 0 <;> simp [em1]
      { simp [lt_iff_le_not_le.mp hx]
        simp [getValSpV_empty spv1 x (by intro i hi; omega)] }
      by_cases em2: spv2.size = 0 <;> simp [em2]
      { intros
        simp [getValSpV_empty spv2 x (by intro i hi; omega)] }
      intro zer_ineq
      have zer_lemma (spv: SpV α κ γ) (i: ℕ) (hsz: spv.size ≠ 0): i < spv.ind[0] → spv[i] = 0 := by
        intro lt
        have all_none: ∀ j < spv.size, spv.ind[j] ≠ i := by
          intro i1 hi1
          by_cases i10 : i1 = 0
          { simp [←i10] at lt
            omega }
          have contra := spv.h_inc 0 i1 (by omega) (by omega) (by omega)
          omega
        simp [getValSpV_empty spv i all_none]
      by_cases sm1: spv1.ind[0] ≤ x
      { simp [sm1] at zer_ineq
        simp [zer_lemma spv2 x em2 zer_ineq] }
      simp at sm1
      simp [zer_lemma spv1 x em1 sm1]

method SpVSpV
  (mut out: Array α)
  (spv1: SpV α κ γ)
  (spv2: SpV α κ γ) return (u: Unit)
  ensures outNew.size = 1
  ensures outNew[0]! = spv_dot spv1 spv2 0 0
  do
    out := Array.replicate 1 0
    let mut pnt1 := 0
    let mut pnt2 := 0
    while pnt1 ≠ spv1.size ∧ pnt2 ≠ spv2.size
    invariant out.size = 1
    invariant pnt1 ≤ spv1.size ∧ pnt2 ≤ spv2.size
    invariant out[0]! + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0
    done_with pnt1 = spv1.size ∨ pnt2 = spv2.size
    do
      if spv1.ind[pnt1] = spv2.ind[pnt2] then
        out[0] += spv1.val[pnt1] * spv2.val[pnt2]
        pnt1 := pnt1 + 1
        pnt2 := pnt2 + 1
      else
        if spv1.ind[pnt1] < spv2.ind[pnt2] then
          pnt1 := pnt1 + 1
        else
          pnt2 := pnt2 + 1
    return
  correct_by by
  { simp [SpVSpV]; mwp
    { cannon }
    cannon }

theorem SpVSpV_correct_triple (out: Array α) (spv1 spv2: SpV α κ γ) (n: ℕ):
  triple
    ((∀ i < spv1.size, spv1.ind[i] < n) ∧ (∀ i < spv2.size, spv2.ind[i] < n))
    (SpVSpV out spv1 spv2)
    fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
      outNew[0]! = ∑ i ∈ Finset.range n, spv1[i] * spv2[i] := by
      simp [triple]
      intro b1 b2
      apply wp_cons (SpVSpV out spv1 spv2)
        fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
          outNew.size = 1 ∧ outNew[0]! = spv_dot spv1 spv2 0 0
      { rintro ⟨_, ⟨outNew, PUnit.unit⟩⟩; simp
        intro sz_eq sum_eq
        simp [sum_eq]
        exact spv_dot_pure spv1 spv2 n b1 b2 }
      simp
      have triple_true := SpVSpV_correct out spv1 spv2
      simp [triple] at triple_true
      exact triple_true

method SpMSpV
  (mut out: Array α)
  (spm: Array (SpV α κ γ))
  (spv: SpV α κ γ) return (u: Unit)
  ensures outNew.size = spm.size
  ensures ∀ i < spm.size, outNew[i]! = spv_dot spm[i]! spv 0 0
  do
    out := Array.replicate spm.size 0
    let mut spmInd : κ := ind_inst.replicate spm.size 0
    let mut spvInd : κ := ind_inst.replicate spm.size 0
    while_some i :| i < spm.size ∧ spmInd[i] < spm[i]!.size ∧ spvInd[i] < spv.size
    invariant ind_inst.size spvInd = spm.size
    invariant ind_inst.size spmInd = spm.size
    invariant out.size = spm.size
    invariant ∀ i < ind_inst.size spmInd, spmInd[i] <= spm[i]!.size
    invariant ∀ i < ind_inst.size spvInd, spvInd[i] <= spv.size
    invariant ∀ i < spm.size, out[i]! + spv_dot spm[i]! spv spmInd[i] spvInd[i] = spv_dot spm[i]! spv 0 0
    done_with ∀ i < spm.size, spmInd[i] = spm[i]!.size ∨ spvInd[i] = spv.size
    do
      let ind_m := spmInd[i]
      let ind_v := spvInd[i]
      if spm[i]!.ind[ind_m] = spv.ind[ind_v] then
        out[i] += spm[i]!.val[ind_m] * spv.val[ind_v]
        spmInd := ind_inst.set i (spmInd[i] + 1) spmInd
        spvInd := ind_inst.set i (spvInd[i] + 1) spmInd
      else
        if spm[i]!.ind[ind_m] < spv.ind[ind_v] then
          spmInd := ind_inst.set i (spmInd[i] + 1) spmInd
        else
          spvInd := ind_inst.set i (spvInd[i] + 1) spmInd
    return
  correct_by by
  { simp [SpMSpV]; mwp
    { cannon }
    cannon }


theorem SpMSpV_correct_triple
  (out: Array α)
  (spm: Array (SpV α κ γ))
  (spv: SpV α κ γ)
  (n: ℕ):
  triple
    (∀ i < spm.size, (∀ j < spm[i]!.size, spm[i]!.ind[j] < n) ∧ (∀ j < spv.size, spv.ind[j] < n))
    (SpMSpV out spm spv)
    fun ⟨_, ⟨outNew, _⟩⟩ =>
      outNew.size = spm.size ∧ ∀ i < spm.size, outNew[i]! = ∑ idx ∈ Finset.range n, spm[i]![idx] * spv[idx] := by
        simp [triple]
        intro inb
        apply wp_cons (SpMSpV out spm spv)
          fun ⟨_, ⟨outNew, _⟩⟩ =>
            outNew.size = spm.size ∧ ∀ i < spm.size, outNew[i]! = spv_dot spm[i]! spv 0 0
        { rintro ⟨_, ⟨outNew, _⟩⟩; simp
          intro sz_eq sum_eq
          simp [sz_eq]
          intro i ib
          simp [←spv_dot_pure spm[i]! spv n (inb i ib).left (inb i ib).right]
          exact sum_eq i ib }
        simp
        have triple_true := SpMSpV_correct out spm spv
        simp [triple] at triple_true
        exact triple_true
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

variable {arrInt} [arr_inst_int: TArray Int arrInt]
variable {arrNat} [arr_inst: TArray Nat arrNat]

set_option trace.profiler true
attribute [local solverHint] TArray.multiSet_swap

method insertionSort
  (mut arr: arrInt) return (u: Unit)
  ensures forall i j, 0 ≤ i ∧ i ≤ j ∧ j < size arr → arrNew[i] ≤ arrNew[j]
  ensures toMultiset arr = toMultiset arrNew
  do
    let arr₀ := arr
    let arr_size := size arr
    if arr_size ≤ 1
    then
      return
    else
      let mut n := 1
      while n ≠ size arr
      invariant size arr = arr_size
      invariant 1 ≤ n ∧ n ≤ size arr
      invariant forall i j, 0 ≤ i ∧ i < j ∧ j <= n - 1 → arr[i] ≤ arr[j]
      invariant toMultiset arr = toMultiset arr₀
      done_with n = size arr
      do
        let mut mind := n
        while mind ≠ 0
        invariant size arr = arr_size
        invariant mind ≤ n
        invariant forall i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i] ≤ arr[j]
        invariant toMultiset arr = toMultiset arr₀
        done_with mind = 0
        do
          if arr[mind] < arr[mind - 1] then
            let left := arr[mind - 1]
            let right := arr[mind]
            arr[mind - 1] := right
            arr[mind] := left
          -- mind := mind - 1
        n := n + 1
      return
  correct_by by
  { dsimp [insertionSort]
    velvet_solve
  }

section squareRoot

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
      done_with x < i * i
      do
        i := i + 1
      return i - 1
  correct_by by
  { dsimp [sqrt]
    velvet_solve }

end squareRoot
