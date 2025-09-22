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

section QSortPartition



def arrayToMultiset (a: Array Int) :=
  (Multiset.ofList a.toList)

lemma sameCardMultisetImpliesSameLengthLists (m1 m2: Multiset Int) : 
    (h: m1 = m2) -> m1.toList.length = m2.toList.length := by
      intro h
      subst h
      simp_all only [Multiset.length_toList]


lemma multiSetSameImpliesSameSize (arr1 arr2: Array Int) : (h: arrayToMultiset arr1 = arrayToMultiset arr2) -> arr1.size = arr2.size := by
  unfold arrayToMultiset 
  intro h
  apply sameCardMultisetImpliesSameLengthLists at h
  simp[*] at h
  grind

@[reducible]
def elemSwap! (arr: Array Int) (idx1 idx2 : Nat) :=
  let arr' := Array.set! arr idx1 (arr[idx2]!)
  let arr'' :=  Array.set! arr' idx2 (arr[idx1]!)
  arr''

@[grind]
lemma elemSwap!_left (arr: Array Int) (l r: Nat) (hl : l < arr.size) (hr: r < arr.size) : 
      (elemSwap! arr l r)[l]! = arr[r]! := by
    simp [elemSwap!]
    unfold Array.setIfInBounds 
    split_ifs with h <;> simp[*]
    · simp [Array.getElem_set]
      intro hlr 
      aesop


@[simp, grind]
lemma elemSwap!_right (arr: Array Int) (l r: Nat) (hl : l < arr.size) (hr: r < arr.size) : 
      (elemSwap! arr l r)[r]! = arr[l]! := by
    simp [elemSwap!]
    unfold Array.setIfInBounds 
    split_ifs with h <;> simp[*]
    · simp [Array.getElem_set]
      aesop


@[simp, grind]
lemma elemSwap!_different (arr: Array Int) (l r: Nat) (k: Nat) (hl : l < arr.size) (hr: r < arr.size) (hkl : ¬ k = l) (hkr : ¬ k = r) (hk : k < arr.size) : 
      (elemSwap! arr l r)[k]! = arr[k]! := by
    simp [elemSwap!]
    unfold Array.setIfInBounds 
    split_ifs with h <;> (simp[*] ; grind)


@[simp, grind]
lemma multiSet_swap! ( arr: Array Int ) ( idx₁ idx₂ : Nat ) ( h_idx₁: idx₁ < arr.size ) ( h_idx₂: idx₂ < arr.size ) :  
    arrayToMultiset (elemSwap! arr idx₁ idx₂) =
    arrayToMultiset arr
    := by classical
    unfold elemSwap!
    unfold arrayToMultiset 
    simp [List.perm_iff_count]
    intro a;
    rw [List.count_set] <;> try simp [*]
    rw [List.count_set] <;> try simp [*]
    simp [List.getElem_set]
    split_ifs with h <;> try simp
    have : Array.count a arr > 0 := by
      apply Array.count_pos_iff.mpr; simp [<-h]
    omega


attribute [local solverHint] multiSet_swap! elemSwap!_left elemSwap!_right elemSwap!_different

method qsortPartition (mut arr: Array Int) (low: Nat) (high: Nat) 
  return (pivotIndex: Nat)
  require low < high ∧ high < arr.size
  ensures low <= pivotIndex ∧ pivotIndex <= high
  ensures arrNew[pivotIndex]! = arr[high]!
  ensures forall k, low <= k ->  k <= pivotIndex -> arrNew[k]! < arrNew[pivotIndex]!
  ensures forall k, pivotIndex < k -> k <= high -> arrNew[k]! >= arrNew[pivotIndex]!
  do
    let oldArr := arr
    let pivotVal := arr[high]!
    let mut i := low
    let mut j := low
    while j < high 
    invariant low <= i ∧ i <= j ∧ j <= high
    invariant arrayToMultiset arr = arrayToMultiset oldArr
    invariant (forall k, low <= k -> k < i -> arr[k]! < pivotVal)
    invariant (forall k , i <= k -> k < j -> arr[k]! >= pivotVal)
    do
      if arr[j]! < pivotVal then
        arr := elemSwap! arr i j
        i := i + 1
      j := j + 1
    let temp_final_swap := arr[i]!
    arr[i] := arr[high]!
    arr[high] := temp_final_swap
    return i
  

/- 
prove_correct qsortPartition by
  unfold qsortPartition 
  loom_solve
  · skip
    have : arrayToMultiset arr_1 = arrayToMultiset  arr := by trivial
    rw [<-this]
    apply multiSet_swap! <;> (apply multiSetSameImpliesSameSize at this ; grind)
  · intros k hlowk hik
    by_cases hik' : k = i
    by_cases hij : k = j
    · subst hik'
      subst hij
      simp[*] 
      unfold Array.setIfInBounds
      split_ifs with hif <;> (simp[*] at *; assumption)
    · subst hik'
      simp[*] at *
      have : ( elemSwap! arr_1 k j )[k]!  = arr_1[j]! := by
        refine elemSwap!_left arr_1 k j ?_ ?_ 
        all_goals (
        have : arr_1.size = arr.size := by 
            apply multiSetSameImpliesSameSize; assumption
        grind)
      grind
    · simp[*]
      have : ( elemSwap! arr_1 i j )[k]!  = arr_1[k]! := by
        refine elemSwap!_different arr_1 i j k ?_ ?_ ?_ ?_ ?_
        all_goals (
        have : arr_1.size = arr.size := by 
            apply multiSetSameImpliesSameSize; assumption
        grind)
      rw [this]
      simp[*] at *
      have : ∀ (k : ℕ), low ≤ k → k < i → arr_1[k]! < arr[high] := by assumption
      apply this
      assumption
      omega
  · intros k hik hkj 
    simp[*]
    have : ( elemSwap! arr_1 i j )[k]!  = arr_1[k]! := by
      refine elemSwap!_different arr_1 i j k ?_ ?_ ?_ ?_ ?_
      all_goals (
      have : arr_1.size = arr.size := by 
          apply multiSetSameImpliesSameSize; assumption
      grind)
    rw [this]
    simp[*] at *
    apply invariant_4
    omega
    sorry
  · intros k hik hkhigh 
    aesop
  · intros k hlowk hki
    sorry
  · sorry

-/
  

-- TODO: Fix, i think there might be some issue in the invariant, look into it
prove_correct qsortPartition by
  loom_solve
  · skip
    have : arrayToMultiset arr_1 = arrayToMultiset  arr := by trivial
    rw [<-this]
    apply multiSet_swap! <;> (apply multiSetSameImpliesSameSize at this ; grind)
  · intros k hlowk hik
    by_cases hik' : k = i
    by_cases hij : k = j
    · subst hik'
      subst hij
      simp[*] 
      unfold elemSwap!
      simp[*]
      unfold Array.setIfInBounds
      split_ifs with hif <;> (simp[*] at *; assumption)
    · subst hik'
      simp[*] at *
      have : ( elemSwap! arr_1 k j )[k]!  = arr_1[j]! := by
        refine elemSwap!_left arr_1 k j ?_ ?_ 
        all_goals (
        have : arr_1.size = arr.size := by 
            apply multiSetSameImpliesSameSize; assumption
        grind)
      grind
    · simp[*]
      have : ( elemSwap! arr_1 i j )[k]!  = arr_1[k]! := by
        refine elemSwap!_different arr_1 i j k ?_ ?_ ?_ ?_ ?_
        all_goals (
        have : arr_1.size = arr.size := by 
            apply multiSetSameImpliesSameSize; assumption
        grind)
      rw [this]
      simp[*] at *
      have : ∀ (k : ℕ), low ≤ k → k < i → arr_1[k]! < arr[high] := by assumption
      apply this
      assumption
      omega
  · intros k hik hkj 
    simp[*]
    have : ( elemSwap! arr_1 i j)[k]!  = arr_1[k]! := by
      refine elemSwap!_different arr_1 i j k ?_ ?_ ?_ ?_ ?_
      all_goals (
      have : arr_1.size = arr.size := by 
          apply multiSetSameImpliesSameSize; assumption
      grind)
    rw [this]
    simp[*] at *
    apply invariant_4
    omega
    sorry
  · intros k hik hkhigh 
    sorry
  · intros k hlowk hki
    sorry
  · sorry

#eval (qsortPartition #[5,4,3,2,0,-1,-5, 1,-3,-2,0] 2 10).run


end QSortPartition
