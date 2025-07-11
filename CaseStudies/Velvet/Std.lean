import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Extension
import CaseStudies.Velvet.Syntax

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

syntax "swap" ident noWs "[" term "]" "," ident noWs "[" term "]" : doElem

macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := TArray.set $idx $val $id:term)
  | `(doElem|$id:ident[$idx:term] += $val:term) =>
    `(doElem| $id:term := TArray.set $idx (($id:term)[$idx] + $val) $id:term)
  | `(doElem|swap $id1:ident[$idx1:term] , $id2:ident[$idx2:term]) =>
    `(doElem|do
      let lhs := $id1:ident[$idx1:term]
      let rhs := $id2:ident[$idx2:term]
      $id1:ident[$idx1] := rhs
      $id2:ident[$idx2] := lhs)
