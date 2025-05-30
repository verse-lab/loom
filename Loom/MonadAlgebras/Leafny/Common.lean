import Lean
import Lean.Parser

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic

import Loom.MonadAlgebras.Leafny.Extension


open PartialCorrectness DemonicChoice

-- method foo (mut x : ℕ) (mut y : ℕ) return (u : Unit)
--   require x = y
--   ensures x = y + 1
--   ensures u = u do
--   pure ()
--   correct_by by sorry

-- #print foo_lemma

-- method bar (mut x : ℕ) (z : ℕ) : Unit :=
--   x := x + z
--   let mut y := x
--   let u <- foo x y
--   foo y x
--   return u

@[spec, loomWpSimp]
def WPGen.pickSuchThat : WPGen (pickSuchThat τ p : NonDetT DivM τ) := by
  refine ⟨fun post => ∀ t, p t -> post t, True, ?_⟩
  intro post _; apply le_of_eq;
  simp [MonadNonDet.wp_pickSuchThat, loomLogicSimp]

attribute [aesop safe cases] Decidable
attribute [-simp] if_true_left Bool.if_true_left ite_eq_left_iff
attribute [loomLogicSimp] ite_self
attribute [aesop unsafe 20% apply] le_antisymm

@[simp]
lemma Array.replicate_get (n : ℕ) [Inhabited α] (a : α) (i : ℕ) (_ : i < n := by omega) :
  (Array.replicate n a)[i]! = a := by
  rw [getElem!_pos, Array.getElem_replicate]; aesop

@[simp]
lemma Array.modify_get (a : Array α) [Inhabited α] (i j : ℕ) (f : α -> α) :
  (a.modify i f)[j]! = if j < a.size then if j = i then f a[j]! else a[j]! else default := by
  by_cases h : j < a.size
  { (repeat rw [getElem!_pos]) <;> try solve | aesop
    rw [@getElem_modify]; aesop }
  repeat rw [getElem!_neg]
  all_goals (try split) <;> solve | omega | aesop

def Array.sumUpTo [Inhabited α] [AddCommMonoid β] (a : Array α) (f : ℕ -> α -> β) (bound : ℕ) : β :=
  ∑ i ∈ Finset.range bound, f i a[i]!

@[simp]
lemma Array.sumUpToSucc [Inhabited α] [AddCommMonoid α] (a : Array α) (f : ℕ -> α -> α) (bound : ℕ) :
  a.sumUpTo f (bound + 1) = a.sumUpTo f bound + f bound a[bound]! := by
  simp [sumUpTo]
  rw [@Finset.sum_range_succ]


instance [Repr α] [FinEnum α] : Repr (α -> Bool) where
  reprPrec p := fun n => Repr.reprPrec (FinEnum.toList α |>.map fun x => (x, p x)) n

instance : Repr (ℕ -> Bool) where
  reprPrec p := fun n => Repr.reprPrec (List.range 10 |>.map fun x => (x, p x)) n
