import Lean
import Lean.Parser

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.Instances.Basic
import Loom.MonadAlgebras.WP.Tactic

import Velvet.Extension

abbrev VelvetM α := NonDetT DivM α

set_option quotPrecheck false in
notation "[totl|" t "]" => open TotalCorrectness TotalCorrectness.DemonicChoice in t
set_option quotPrecheck false in
notation "[part|" t "]" => open PartialCorrectness PartialCorrectness.DemonicChoice in t

@[local simp]
lemma DivM.total_decompose (α : Type) (x : DivM α) (post₁ post₂ : α -> Prop) :
  ([totl| wp x post₁] ∧ [part| wp x post₂]) = [totl| wp x (post₁ ⊓ post₂)] := by
    simp [[totl| DivM.wp_eq], [part| DivM.wp_eq]]
    split <;> simp

@[local simp, loomLogicSimp]
lemma mimpl (x : NonDetT DivM α) (post₁ post₂ : α -> Prop) :
  (post₁ ≤ post₂) → ([totl|wp x post₁]) ≤ ([part| wp x post₂]) := by
    intro le
    simp [loomLogicSimp]
    simp [loomLogicSimp] at le
    sorry

lemma VelvetM.total_decompose {α : Type} (x : VelvetM α) (post₁ post₂ : α -> Prop):
  [totl| wp x post₁] ⊓ [part| wp x post₂] = [totl| wp x (post₁ ⊓ post₂)] := by
    unhygienic induction x <;> try simp [loomLogicSimp]
    { simp [DivM.total_decompose]
      simp [[totl| DivM.wp_eq], [part| DivM.wp_eq]]
      split
      { simp }
      rename_i arg
      have ind := f_ih arg post₁ post₂
      simp at ind
      rw [ind]
      trivial }
    { constructor <;> intro hyp
      { intro i hi
        have hl := hyp.left i hi
        have hr := hyp.right i hi
        have ind := f_ih i post₁ post₂
        simp [hl] at ind
        simp [hr] at ind
        exact ind }
      constructor <;>
      { intro i hi
        have conj := hyp i hi
        have ind := f_ih i post₁ post₂
        simp [loomLogicSimp] at ind
        rw [←ind] at conj
        simp [conj] } }
    constructor
    { intro conj
      sorry }
    intro hyp
    rcases hyp with ⟨inv, x_ex, h_inv⟩
    rcases x_ex with ⟨x, hx⟩
    simp [spec]
    simp [spec] at h_inv
    simp [LE.pure] at h_inv
    constructor
    { exists inv
      constructor
      { exists x }
      simp [h_inv]
      simp [LE.pure]
      exact le_trans h_inv.right (by
        have st: ∀ x, (post₁ x ∧ post₂ x) ≤ post₁ x := by
          intro x
          simp
          intro hx hy
          exact hx
        simp [←[totl| NonDetT.wp_eq_wp], ←[part| NonDetT.wp_eq_wp]]
        simp [loomLogicSimp]
        intro x and_wp
        have cont_ind := cont_ih x post₁ post₂
        simp [loomLogicSimp] at cont_ind
        simp [and_wp] at cont_ind
        simp [cont_ind] ) }
    exists inv
    constructor
    { intro b hb
      have hbx := hx b hb
      simp [←[totl| NonDetT.wp_eq_wp]] at hbx
      have hbxf := fun x_1 ↦
        match x_1 with
        | ForInStep.yield b' => inv (ForInStep.yield b') ∧ x b' < x b
        | ForInStep.done b' => inv (ForInStep.done b')
      have hb_triv: True ≤ ([totl| wp (f b) fun x_1 ↦
        match x_1 with
        | ForInStep.yield b' => inv (ForInStep.yield b') ∧ x b' < x b
        | ForInStep.done b' => inv (ForInStep.done b')]) := by
        simp [loomLogicSimp]
        exact hbx
      have tr_intro: True ≤ ([part| NonDetT.wp (f b) inv]) := le_trans hb_triv (by
        simp [loomLogicSimp]
        intro wp_x
        simp [←[part| NonDetT.wp_eq_wp]]
        apply mimpl (f b) (fun x_1 ↦
          match x_1 with
          | ForInStep.yield b' => inv (ForInStep.yield b') ∧ x b' < x b
          | ForInStep.done b' => inv (ForInStep.done b')) (fun x => inv x)
        { simp [loomLogicSimp]
          intro x1
          match x1 with
          | ForInStep.yield b' => simp; intros; simp [*]
          | ForInStep.done b' => simp }
        exact wp_x)
      simp at tr_intro
      simp [tr_intro] }
    simp [LE.pure]
    simp [h_inv]
    exact le_trans h_inv.right (by
      simp [←[totl| NonDetT.wp_eq_wp], ←[part| NonDetT.wp_eq_wp]]
      simp [loomLogicSimp]
      /-intro x and_wp
      have cont_ind := cont_ih x post₁ post₂
      simp [loomLogicSimp] at cont_ind
      simp [and_wp] at cont_ind
      simp [cont_ind]-/)



section
open PartialCorrectness DemonicChoice

@[spec, loomWpSimp]
noncomputable
def WPGen.pickSuchThat [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l]
  [MPropOrdered m l] : WPGen (pickSuchThat τ p : NonDetT m τ) := by
  refine ⟨fun post => ⨅ t, ⌜p t⌝ ⇨ post t, ?_⟩
  intro post;
  simp [MonadNonDet.wp_pickSuchThat, loomLogicSimp]

attribute [aesop safe cases] Decidable
attribute [-simp] if_true_left Bool.if_true_left ite_eq_left_iff
attribute [loomLogicSimp] ite_self
attribute [aesop unsafe 20% apply] le_antisymm
end

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
