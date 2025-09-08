import Auto
import Lean
import Std.Data.HashMap

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Extension
import CaseStudies.Velvet.Syntax

class Setter (cont : Type) (idx : Type) (elem : Type) where
  set : idx → elem → cont → cont

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

  append : κ → κ → κ
  size_append (arr1 arr2 : κ) : size (append arr1 arr2) = size arr1 + size arr2
  get_append_left (arr1 arr2 : κ) (i : Nat) (h : i < size arr1) : get i (append arr1 arr2) = get i arr1
  get_append_right (arr1 arr2 : κ) (i : Nat) (h1 : size arr1 ≤ i) (h2 : i < size arr1 + size arr2) : get i (append arr1 arr2) = get (i - size arr1) arr2

  slice : Nat → Nat → κ → κ
  size_slice (start len arr) : size (slice start len arr) = (min (start + len) (size arr)) - (min start (size arr))
  get_slice (start len arr) (i : Nat) (h_i : i < size (slice start len arr)) : get i (slice start len arr) = get (start + i) arr

  foldl {β : Type} (f : β → α → β) (init : β) (arr : κ) : β
  foldr {β : Type} (f : α → β → β) (init : β) (arr : κ) : β
  filter (p : α → Bool) (arr : κ) : κ
  size_filter_le (p : α → Bool) (arr : κ) : size (filter p arr) ≤ size arr
  to_list: κ -> List α
  to_list_same_sz arr : size arr = List.length ( to_list arr )
  to_list_eqv (arr: κ) (i: Nat) (hi: i < size arr) : get i arr = ( to_list arr ).get (⟨i, (by grind)⟩) 

def Array.get_set_c [Inhabited α] (i j: Nat) (val: α) (arr: Array α):
  i < arr.size → (arr.set! j val)[i]! = if i = j then val else arr[i]! := by
    intro h
    by_cases h' : j < arr.size
    { simp [Array.setIfInBounds, dif_pos h']
      rw [getElem!_pos, getElem!_pos] <;> try simp [*]
      rw [@Array.getElem_set]; aesop }
    simp [Array.setIfInBounds, dif_neg h']
    rw [getElem!_pos] <;> try simp [*]
    omega

def Array.size_set_c [Inhabited α] (i: Nat) (val: α) (arr: Array α):
  (arr.set! i val).size = arr.size := by simp

def Array.multiset_swap [Inhabited α]
(arr: Array α) (idx₁ idx₂: Nat) (h_idx₁: idx₁ < arr.size) (h_idx₂: idx₂ < arr.size) :
  Multiset.ofList ((arr.set! idx₂ arr[idx₁]!).set! idx₁ arr[idx₂]!).toList = Multiset.ofList arr.toList := by
    classical
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

instance [Inhabited α] : TArray α (Array α) where
  get i arr := arr[i]!
  set i val arr := arr.set! i val
  size arr := arr.size
  get_set := Array.get_set_c
  size_set := Array.size_set_c
  replicate sz elem := Array.replicate sz elem
  replicate_size sz elem := by simp
  replicate_get sz elem i h_i := by rw [getElem!_pos] <;> try simp [*]
  toMultiset arr := Multiset.ofList arr.toList
  multiSet_swap := Array.multiset_swap
  append arr1 arr2 := arr1 ++ arr2
  size_append arr1 arr2 := by simp [Array.size_append]
  get_append_left arr1 arr2 i h := by
    have : i < (arr1 ++ arr2).size := by simp_all [Array.size_append]; omega
    aesop
  get_append_right arr1 arr2 i h1 h2 := by
    have : i < (arr1 ++ arr2).size := by simp_all [Array.size_append]
    have : i - arr1.size < arr2.size := by simp_all [Array.size_append]; omega
    aesop
  slice start len arr := arr.extract start (start + len)
  size_slice start len arr := by 
    simp [Array.size_extract]
    grind
  get_slice start len arr i h_i := by
    have : start + i < arr.size := by simp_all [Array.size_extract]; omega
    simp [Array.getElem_extract, *]
    aesop
  foldl f init arr := arr.foldl f init
  foldr f init arr := arr.foldr f init
  filter p arr := arr.filter p
  size_filter_le p arr := by simp [Array.size_filter_le]
  to_list arr := arr.toList
  to_list_same_sz arr :=   by
    grind
  to_list_eqv arr i hi := by
    simp[*]

attribute [solverHint] TArray.get_set TArray.size_set TArray.size_append TArray.size_slice

export TArray (get set size toMultiset append slice)

instance [TArray α κ] : Setter κ Nat α where
  set := TArray.set

class TMap (κ : Type) (α β : outParam Type) [BEq α] [Hashable α] [Inhabited β] where
  get : α → κ → β
  set : α → β → κ → κ
  remove : α → κ → κ
  get_set_eq (k : α) (v : β) (m : κ) : get k (set k v m) = v
  get_set_ne (k₁ k₂ : α) (v : β) (m : κ) (h : k₁ ≠ k₂) : get k₁ (set k₂ v m) = get k₁ m
  get_remove_eq (k : α) (m : κ) : get k (remove k m) = default
  get_remove_ne (k₁ k₂ : α) (m : κ) (h : k₁ ≠ k₂) : get k₁ (remove k₂ m) = get k₁ m
  empty : κ
  get_empty (k : α) : get k empty = default
  to_list : κ → List (α × β)
  fold {γ : Type} (f : γ → α → β → γ) (init : γ) (m : κ) : γ

instance [BEq α] [LawfulBEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] [Inhabited β]  : TMap (Std.HashMap α β) α β where
  get k m := m[k]!
  set k v m := m.insert k v
  remove k m := m.erase k
  get_set_eq k v m := by
    simp
  get_set_ne k₁ k₂ v m h := by 
    rw [Std.HashMap.getElem!_insert]
    grind
  get_remove_eq k m := by simp [Std.HashMap.getD_erase]
  get_remove_ne k₁ k₂ m h := by 
    grind
  empty := Std.HashMap.emptyWithCapacity
  get_empty k := by grind
  to_list m := m.toList
  fold f init m := m.fold (fun acc k v => f acc k v) init

attribute [solverHint] TMap.get_set_eq TMap.get_set_ne TMap.get_remove_eq TMap.get_remove_ne TMap.get_empty

export TMap (get set remove empty to_list fold)

instance [BEq α] [Hashable α] [Inhabited β] [TMap κ α β] : Setter κ α β where
  set := TMap.set

instance [TArray α κ] : GetElem κ Nat α fun _ _ => True where
  getElem inst i _ := TArray.get i inst

instance [BEq α] [Hashable α] [Inhabited β] [TMap κ α β] : GetElem κ α β fun _ _ => True where
  getElem inst k _ := TMap.get k inst

instance [Inhabited α] [TArray α κ] : Inhabited κ where
  default := TArray.replicate 0 default

@[loomAbstractionSimp]
lemma getElemE (α κ) {_ : TArray α κ} (k : κ) : k[i] = get i k := by
  rfl

syntax (priority := high + 1) ident noWs "[" term "]" ":=" term : doElem
syntax (priority := high + 1) ident noWs "[" term "]" "+=" term : doElem

syntax "swap" ident noWs "[" term "]" ident noWs "[" term "]" : doElem
syntax "swap!" ident noWs "[" term "]" "!" ident noWs "[" term "]" "!" : doElem

macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := Setter.set $idx $val $id:term)
  | `(doElem|$id:ident[$idx:term] += $val:term) =>
    `(doElem| $id:term := Setter.set $idx (($id:term)[$idx] + $val) $id:term)
  | `(doElem|swap $id1:ident[$idx1:term] $id2:ident[$idx2:term]) =>
    `(doElem|do
      let lhs := $id1:ident[$idx1:term]
      let rhs := $id2:ident[$idx2:term]
      $id1:ident[$idx1] := rhs
      $id2:ident[$idx2] := lhs)
  | `(doElem|swap! $id1:ident[$idx1:term]! $id2:ident[$idx2:term]!) =>
    `(doElem|do
      let lhs := $id1:ident[$idx1:term]!
      let rhs := $id2:ident[$idx2:term]!
      $id1:ident := ($id1:ident).set! $idx1:term rhs
      $id2:ident := ($id2:ident).set! $idx2:term lhs)
