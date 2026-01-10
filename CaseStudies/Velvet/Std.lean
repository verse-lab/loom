import Auto
import Lean
import Std.Data.HashMap

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.Options
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Extension
import CaseStudies.Velvet.Syntax


macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := Array.set! $id:term $idx $val )
  | `(doElem|$id:ident[$idx:term] += $val:term) =>
    `(doElem| $id:term := Array.set! $id:term $idx (($id:term)[$idx]! + $val))
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

theorem Array.get_set_c [Inhabited α] (i j: Nat) (val: α) (arr: Array α):
  i < arr.size → (arr.set! j val)[i]! = if i = j then val else arr[i]! := by
    intro h
    by_cases h' : j < arr.size
    { simp [Array.setIfInBounds, dif_pos h']
      rw [getElem!_pos, getElem!_pos] <;> try simp [*]
      rw [@Array.getElem_set]; aesop }
    simp [Array.setIfInBounds, dif_neg h']
    rw [getElem!_pos] <;> try simp [*]
    omega

attribute [grind =]
  Array.get_set_c

lemma add_mod_elim (m n: Nat) {a b : Nat} (hm: m > 0) (h: (a + n) % m = (b + n) % m): a % m = b % m := by
  nth_rw 1 [←Nat.add_mod_mod] at h
  nth_rw 2 [←Nat.add_mod_mod] at h
  have hyp := Nat.add_mod_eq_add_mod_right (m - n % m) h
  repeat rw [add_assoc] at hyp
  have : n % m + (m - n % m) = m := by
    rw [←Nat.add_sub_assoc, Nat.add_sub_cancel_left]
    have lem := Nat.mod_lt n hm
    omega
  simp [this] at hyp
  exact hyp

def Array.toMultiset (arr : Array α) := Multiset.ofList arr.toList

theorem Array.multiset_swap [Inhabited α]
(arr: Array α) (idx₁ idx₂: Nat) (h_idx₁: idx₁ < arr.size) (h_idx₂: idx₂ < arr.size) :
  ((arr.set! idx₂ arr[idx₁]!).set! idx₁ arr[idx₂]!).toMultiset = arr.toMultiset := by
    classical
    simp [List.perm_iff_count, Array.toMultiset]
    intro a;
    rw [getElem!_pos,getElem!_pos] <;> try simp [*]
    rw [List.count_set] <;> try simp [*]
    rw [List.count_set] <;> try simp [*]
    simp [List.getElem_set]
    split_ifs with h <;> try simp
    have : Array.count a arr > 0 := by
      apply Array.count_pos_iff.mpr; simp [<-h]
    omega

@[app_unexpander WithName] def unexpandWithName : Lean.PrettyPrinter.Unexpander
  | `($(_) $p:term) => `($p:term)
  | `($(_) $p:term $_) => `($p:term)
  | _ => throw ()
@[app_unexpander WithName.mk'] def unexpandWithNameMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $p:term) => `($p:term)
  | `($(_) $p:term $_) => `($p:term)
  | _ => throw ()
