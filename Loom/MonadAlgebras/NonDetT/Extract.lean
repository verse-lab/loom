import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.W.Basic
import Mathlib.Data.FinEnum

import Loom.MonadAlgebras.WP.Gen
import Loom.MonadAlgebras.WP.Liberal
import Loom.MonadAlgebras.NonDetT.Basic
import Loom.MonadAlgebras.NonDetT.Findable

universe u v w

open Lean.Order

variable [Monad m] [CCPOBot m] [CompleteBooleanAlgebra l] [MAlgOrdered m l] [LawfulMonad m]
variable [∀ α, CCPO (m α)] [MonoBind m]

def NonDetT.run {α : Type u} :  NonDetT m α -> m α
  | .pure x => Pure.pure x
  | .vis x f => liftM x >>= (fun x => (f x).run)
  | @NonDetT.pickCont _ _ _ p _ f =>
    match Findable.find (p := p) () with
    | none => CCPOBot.compBot
    | some x =>  (f x).run
  | .repeatCont init f cont =>
    forIn Lean.Loop.mk init (fun _ x => (f x).run) >>= (fun x => (cont x).run)


namespace PartialCorrectness.DemonicChoice

variable [MAlgPartial m] [CCPOBotLawful m]

lemma ExtractNonDet.extract_refines_wp (s : NonDetT m α) :
  wp s post <= wp s.run post := by
  unhygienic induction s
  { simp [wp_pure, NonDetT.run] }
  { simp [NonDetT.wp_vis, NonDetT.run, wp_bind]
    apply wp_cons; aesop (add norm inf_comm) }
  { simp [NonDetT.wp_pickCont, NonDetT.run]; split
    { have := Findable.find_none (p := p) (by simpa);
      have : (∀ x, p x = False) := by simpa
      simp [this]
      simp [CCPOBotLawful.prop, wp_bot] }
    rename_i y _
    refine iInf_le_of_le y ?_
    have := Findable.find_some_p (p := p) (by assumption)
    simp [this]; apply f_ih }
  rw [NonDetT.wp_repeatCont, NonDetT.run, wp_bind]
  simp; intro inv hinv; apply le_trans'; apply wp_cons; rotate_right
  { apply (triple_spec ..).mpr; apply repeat_inv
    intro b; apply le_trans'; apply f_ih
    simp [NonDetT.wp_eq_wp, hinv] }
  intro b; apply le_trans'; apply cont_ih
  simp [NonDetT.wp_eq_wp]

lemma ExtractNonDet.extract_refines (pre : l) (s : NonDetT m α) :
  triple pre s post ->
  triple pre s.run post := by
  intro tr; apply le_trans'; apply ExtractNonDet.extract_refines_wp
  aesop

end PartialCorrectness.DemonicChoice

namespace TotalCorrectness.DemonicChoice

lemma ExtractNonDet.extract_refines_wp (s : NonDetT m α) :
  wp s post <= wp s.run post := by
  unhygienic induction s
  { simp [wp_pure, NonDetT.run] }
  { simp [NonDetT.wp_vis, NonDetT.run, wp_bind]
    apply wp_cons; aesop (add norm inf_comm) }
  { simp [NonDetT.wp_pickCont, NonDetT.run]; split
    { have := Findable.find_none (p := p) (by simpa);
      have : (∀ x, p x = False) := by simpa
      simp [this] }
    intro _ _
    rename_i y _ _ _
    refine iInf_le_of_le y ?_
    have := Findable.find_some_p (p := p) (by assumption)
    simp [this]; apply f_ih }
  rw [NonDetT.wp_repeatCont, NonDetT.run, wp_bind]
  simp; intro inv wf hinv; apply le_trans'; apply wp_cons; rotate_right
  { apply (triple_spec ..).mpr; apply repeat_inv
    intro b; apply le_trans'; apply f_ih
    simp [NonDetT.wp_eq_wp]
    apply hinv }
  intro b; apply le_trans'; apply cont_ih
  simp [NonDetT.wp_eq_wp]

lemma ExtractNonDet.extract_refines (pre : l) (s : NonDetT m α) :
  triple pre s post ->
  triple pre s.run post := by
  intro tr; apply le_trans'; apply ExtractNonDet.extract_refines_wp
  aesop

end TotalCorrectness.DemonicChoice
