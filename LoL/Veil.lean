import LoL.MProp.Instances
import LoL.MProp.NonDetT

import LoL.Meta

set_option autoImplicit true

namespace Veil

abbrev ExecDet (σ ρ : Type) := ExceptT Int (StateT σ Id) ρ
abbrev Exec (σ ρ : Type) := NonDetT (ExecDet σ) ρ

def assertionFailedId : Int := 0
def otherId : Int := 1
-- #gen_spec assertE' (σ α : Type) for
--   wp (m := ExecDet σ) (α := α) (StateT.lift (.mk (.error "assertion failed")))
section
-- variable
#gen_spec getE (σ : Type) (hd : Int -> Prop) (hd' : IsHandler hd) for wp (liftM (m := StateT σ Id) (n :=  ExecDet σ) (StateT.get))
#gen_spec setE (σ : Type) (s : σ) (hd : Int -> Prop) (hd' : IsHandler hd) for wp (liftM (m := StateT σ Id) (n :=  ExecDet σ) (StateT.set s))

end

lemma iInfE : iInf (α := σ -> Prop) f = fun x => ∀ y, f y x := by ext; simp
lemma iSupE : iSup (α := σ -> Prop) f = fun x => ∃ y, f y x := by ext; simp
lemma complE : (fᶜ : σ -> Prop) = fun x => ¬ f x := by ext; simp

lemma topE : (⊤ : σ -> Prop) = fun _ => True := by rfl
lemma botE : (⊥ : σ -> Prop) = fun _ => False := by rfl
@[simp]
lemma if_fun [Decidable cnd] (tf ef : α -> β) :
  (if cnd then fun x => tf x else fun x => ef x) = fun x => if cnd then tf x else ef x := by
  split_ifs <;> rfl
@[wpSimp]
lemma if_app {α β} p [Decidable p] (t e : α -> β)  : (if p then t else e) = fun x => if p then t x else e x := by
  split <;> rfl
@[simp]
lemma not_if {_ : Decidable p} (t e : Prop) : (¬ (if p then t else e)) = if p then ¬ t else ¬ e := by
  split_ifs <;> simp

def assert (as : Prop) [Decidable as] [Monad m] [MonadExcept Int m] : m Unit := do
  do unless as do throw assertionFailedId

lemma assertE {σ} (as : Prop) [Decidable as] :
  assert (m := Exec σ) as = liftM (assert (m := ExecDet σ) as) := by sorry

lemma pureE {σ ρ} (x : ρ) :
  pure (f := Exec σ) x = NonDetT.pure x := rfl

section
-- open Demonic
-- namespace Demonic

open Demonic in
@[wpSimp]
lemma wpAssertED [Decidable as] (hd : Int -> Prop) (_ : IsHandler hd) :
  wp (assert (m := Exec σ) as) post = fun s => if as then post .unit s else hd assertionFailedId := by
    simp [assertE, NonDetT.wp_lift]
    simp [assert]; split_ifs <;> try simp [wpSimp, wp_pure]
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk]
    erw [wp_except_handler_eq, wp_pure]; simp_all; rfl

open Angelic in
@[wpSimp]
lemma wpAssertEA [Decidable as] (hd : Int -> Prop) (_ : IsHandler hd) :
  wp (assert (m := Exec σ) as) post = fun s => if as then post .unit s else hd assertionFailedId := by
    simp [assertE, NonDetT.wp_lift]
    simp [assert]; split_ifs <;> try simp [wpSimp, wp_pure]
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk]
    erw [wp_except_handler_eq, wp_pure]; simp_all; rfl

open Demonic in
@[wpSimp]
lemma wpGetED (hd : Int -> Prop) (_ : IsHandler hd) :
  wp (get (m := Exec σ)) post = fun s => post s s := by
    ext s; simp only [get, getThe, MonadStateOf.get, @NonDetT.wp_lift, wpSimp]

open Angelic in
@[wpSimp]
lemma wpGetEA (hd : Int -> Prop) (_ : IsHandler hd) :
  wp (get (m := Exec σ)) post = fun s => post s s := by
    ext s; simp only [get, getThe, MonadStateOf.get, @NonDetT.wp_lift, wpSimp]

open Demonic in
@[wpSimp]
lemma wpSetED (hd : Int -> Prop) (_ : IsHandler hd) :
  wp (set (σ := σ) (m := Exec σ) s) post = fun _ => post .unit s := by
    ext s; simp only [set, MonadStateOf.set, NonDetT.wp_lift, wpSimp]

open Angelic in
@[wpSimp]
lemma wpSetEA (hd : Int -> Prop) (_ : IsHandler hd) :
  wp (set (σ := σ) (m := Exec σ) s) post = fun _ => post .unit s := by
    ext s; simp only [set, MonadStateOf.set, NonDetT.wp_lift, wpSimp]

-- end Demonic
end



variable {σ ρ : Type}

def nonDet : Exec Nat Unit := do
  let b₁ <- pick Bool
  let b₂ <- pick Bool
  if b₁ then
    if b₂ then
      assert False
    else
      set ((<-get) + 1)
  else
    if b₂ then
      assume False
    else
      set ((<-get) - 1)

def nonDetQ : Exec Nat Bool := do
  let b₁ <- pick Bool
  if b₁ then
    let b₂ <- pick Bool
    return b₂
  return false

def nonDet' : Exec Nat Unit := do
  let b₁ <- pick Bool
  let b₂ <- pick Bool
  if b₁ then
    if b₂ then
      assert False
    else
      set ((<-get) + 1)
  else
    if b₂ then
      throw otherId
    else
      set ((<-get) - 1)


open Classical in
def nonDet'' (tp : Type) (p : tp -> Bool) : Exec Nat Unit := do
  if ∀ x : tp, p x then return ()


lemma classicalE (P : Prop) [inst : Decidable P] : Classical.propDecidable P = inst := by
  cases inst <;> cases h: (Classical.propDecidable P) <;> solve_by_elim



example (P : _ -> Prop) : P nonDet.finally := by
  simp only [nonDet, NonDetT.ite_eq, assertE, pureE]
  dsimp [bind, NonDetT.pure, NonDetT.finally]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  unfold NonDetT.ite; dsimp
  simp [pick_tpc,
        assume_tpc,
        lift_tpc,
        assume_pre,
        lift_pre,
        lift_sem,
        pick_sem,
        pick_pre,
        wp_pure,
        assume_sem,
        Id, bind_pure
        ]
  unfold pick; simp [instMonadNonDetNonDetT, NonDetT.pick]
  sorry

example (P : _ -> Prop) : P nonDetQ.finally := by
  simp only [nonDetQ, NonDetT.ite_eq, assertE, pureE]
  dsimp [bind, NonDetT.pure, NonDetT.finally]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  unfold NonDetT.ite; dsimp
  simp [pick_tpc,
        assume_tpc,
        lift_tpc,
        assume_pre,
        lift_pre,
        lift_sem,
        pick_sem,
        pick_pre,
        wp_pure,
        assume_sem,
        Id, bind_pure
        ]
  unfold pick; simp [instMonadNonDetNonDetT, NonDetT.pick]
  sorry


section
open Demonic

attribute [wpSimp] wp_bind MonadNonDet.wp_pick MonadNonDet.wp_assume

open TotalCorrectness in
example (P : _ -> Prop) : P (wp nonDet post) := by
  simp [nonDet, wpSimp, iInfE]
  sorry

section
open PartialCorrectness
example (P : _ -> Prop) : P (wp nonDet post) := by
  simp [nonDet, wpSimp, iInfE]
  sorry

example (P : _ -> Prop) : P (iwp nonDet post) := by
  simp [iwp, nonDet, wpSimp, iInfE, complE]
  sorry

def tr (c : Exec σ α) (s s' : σ) (r' : α) := iwp c (· = r' ∧ · = s') s

example (P : _ -> Prop) : P (tr nonDet s s') := by
  unfold tr
  simp [iwp, nonDet, wpSimp, iSupE]
  sorry
end

open Demonic
example (ex : Int)  s : [handler (· ≠ ex)|wp nonDet' ⊤ s ] := by
  simp [nonDet', wpSimp, iSupE, throw, throwThe, MonadExceptOf.throw, ExceptT.mk,
    NonDetT.wp_lift]
  erw [wp_except_handler_eq, wp_pure, MPropOrdered.pure, pure, Applicative.toPure, Monad.toApplicative];
  simp [StateT.instMonad,MPropOrdered.μ, StateT.pure]
  sorry


end

section
open Angelic

attribute [wpSimp] wp_bind MonadNonDet.wp_pick MonadNonDet.wp_assume

section
open TotalCorrectness
example (P : _ -> Prop) : P (wp nonDet post) := by
  simp [nonDet, wpSimp, iSupE]
  sorry

def tr' (c : Exec σ α) (s s' : σ) (r' : α) := wp c (· = r' ∧ · = s') s

example (P : _ -> Prop) : P (tr' nonDet s s' r') := by
  unfold tr'
  simp [nonDet, wpSimp, iSupE]
  sorry

end

open PartialCorrectness in
example (P : _ -> Prop) : P (wp nonDet post) := by
  simp [nonDet, wpSimp, iSupE]
  sorry


end

end Veil
