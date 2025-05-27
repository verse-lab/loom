import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Mathlib.Data.W.Basic
import Mathlib.Data.FinEnum

import LoL.MonadAlgebras.WP.Gen
import LoL.MonadAlgebras.WP.Liberal
import LoL.MonadAlgebras.NonDetT.Basic

universe u v w

open ExceptionAsFailure Lean.Order

inductive AccFrom (p : Nat -> Prop) : Nat -> Prop
    | now : p i -> AccFrom p i
    | later : ¬ p i -> AccFrom p (i + 1) -> AccFrom p i


def findNat (p : Nat -> Prop) [DecidablePred p] : Option Nat :=
  let rec aux i :=
    if p i then
      some i
    else
      aux (i + 1)
  partial_fixpoint
  aux 0

lemma AccFrom_findNat (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  AccFrom p i -> (findNat.aux p i).isSome := by
  intros h; unhygienic induction h <;> (unfold findNat.aux; aesop)

lemma AccFrom_of_p (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  p i -> ∀ j ≤ i, AccFrom p j := by
  intro pi j h
  unhygienic induction h using Nat.decreasingInduction <;> try solve_by_elim
  by_cases p k; solve_by_elim
  apply AccFrom.later <;> solve_by_elim

lemma exists_findNat (p : Nat -> Prop) [DecidablePred p] :
  (∃ x, p x) ↔ (findNat p).isSome := by
  constructor
  { rintro ⟨x, px⟩
    apply AccFrom_findNat; apply AccFrom_of_p <;> aesop }
  simp [Option.isSome_iff_exists]; intro i eq; exists i; revert eq
  unfold findNat; generalize 0 = m;
  apply findNat.aux.partial_correctness; aesop

lemma findNat_none (p : Nat -> Prop) [DecidablePred p] :
  (findNat p).isNone -> ∀ i, ¬ p i := by
  simp; rw [<-Option.not_isSome_iff_eq_none, <-exists_findNat]; simp

lemma findNat_aux_some_le (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  findNat.aux p i = some j -> ∀ k, i <= k -> k < j -> ¬ p k := by
  apply findNat.aux.partial_correctness
  intro aux ih i r; split
  { rintro ⟨⟩ ph; omega }
  intro h; have:= ih _ _ h;
  intros k _ _ pk; apply this k <;> try omega
  by_cases h : k = i; aesop; omega

lemma findNat_some_p (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  findNat p = some i -> p i := by
  simp [findNat]; generalize 0 = m;
  apply findNat.aux.partial_correctness; aesop

lemma p_findNat_some (p : Nat -> Prop) [DecidablePred p] (i : Nat) :
  p i -> ∃ j, p j ∧ j <= i ∧ findNat p = some j := by
  intro pi;
  have : (findNat p).isSome := by
    false_or_by_contra; rename_i h
    simp [<-Option.isNone_iff_eq_none] at h
    have h := findNat_none _ h
    aesop
  revert this; simp [Option.isSome_iff_exists]
  intro x h
  have := findNat_aux_some_le p 0 h
  exists x; repeat' constructor
  { solve_by_elim [findNat_some_p] }
  { have h := fun h₁ h₂ => this _ h₁ h₂ pi
    simp at h; exact h }
  solve_by_elim

def find [Encodable α] (p : α -> Prop) [DecidablePred p] : Option α :=
  findNat (fun x => (Encodable.decode x).any (p ·)) |>.bind Encodable.decode

lemma find_none (p : α -> Prop) [DecidablePred p] [Encodable α] :
  (find p).isNone -> ∀ x, ¬ p x := by
  simp [find]; intro h a pa
  have := p_findNat_some (fun x => (Encodable.decode x).any (p ·)) (Encodable.encode a) ?_
  { rcases this with ⟨j, pj, hj, eq⟩; simp [eq] at h;
    simp [h] at pj }
  simpa

lemma find_some_p (p : α -> Prop) [DecidablePred p] [Encodable α] (x : α) :
  find p = some x -> p x := by
  simp [find, Option.bind]; split; simp
  have := findNat_some_p _ _ (by assumption)
  intro eq; rw [eq] at this; simp at this; exact this

class WeakFindable {α : Type u} (p : α -> Prop) where
  find : Option α
  find_some_p : find = some x -> p x

class Findable {α : Type u} (p : α -> Prop) where
  find : Option α
  find_none : find.isNone -> ∀ x, ¬ p x
  find_some_p : find = some x -> p x

instance WeakFindable.of_Findable {α : Type u} (p : α -> Prop) [Findable p] : WeakFindable p where
  find := Findable.find p
  find_some_p := Findable.find_some_p

instance {p : α -> Prop} [Encodable α] [DecidablePred p] : Findable p where
  find := find p
  find_none := find_none p
  find_some_p := find_some_p p _

@[instance high]
instance {p : α -> Prop} [FinEnum α] [DecidablePred p] : Findable p where
  find := FinEnum.toList α |>.find? p
  find_none := by simp [List.find?, Fintype.complete]
  find_some_p := by intro x h; have := List.find?_some h; aesop

inductive ExtractNonDet (findable : {τ : Type u} -> (τ -> Prop) -> Type u) {m} : {α : Type u} -> NonDetT m α -> Type _ where
  | pure {α} : ∀ (x : α), ExtractNonDet findable (NonDetT.pure x)
  | vis {α} {β} (x : m β) (f : β → NonDetT m α) :
      (∀ y, ExtractNonDet findable (f y)) → ExtractNonDet findable (.vis x f)
  | pickSuchThat {α} (τ : Type u) (p : τ -> Prop) (f : τ → NonDetT m α)
    {_ : findable p}
     : (∀ x, ExtractNonDet findable (f x)) → ExtractNonDet findable (.pickCont τ p f)
  | assume {α} (p : PUnit -> Prop) (f : PUnit → NonDetT m α) :
    (∀ x, ExtractNonDet findable (f x)) → ExtractNonDet findable (.pickCont PUnit p f)
  | repeatCont {α} {β} init (f : β -> NonDetT m (ForInStep β)) (cont : β -> NonDetT m α) :
     (∀ x, ExtractNonDet findable (f x)) →
     (∀ x, ExtractNonDet findable (cont x)) →
     ExtractNonDet findable (.repeatCont init f cont)

set_option linter.unusedVariables false in
def ExtractNonDet.bind {findable : {τ : Type u} -> (τ -> Prop) -> Type u} :
  (_ : ExtractNonDet findable x) -> (_ : ∀ y, ExtractNonDet findable (f y)) -> ExtractNonDet findable (x >>= f)
  | .pure x, inst => by
    dsimp [Bind.bind, NonDetT.bind]; exact (inst x)
  | .vis x f inst, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; constructor
    intro y; apply ExtractNonDet.bind <;> solve_by_elim
  | .pickSuchThat _ p f inst, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; constructor
    assumption; intro y; apply ExtractNonDet.bind <;> solve_by_elim
  | .assume _ f inst, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; apply ExtractNonDet.assume
    intro y; apply ExtractNonDet.bind <;> solve_by_elim
  | .repeatCont init f cont inst₁ inst₂, inst' => by
    dsimp [Bind.bind, NonDetT.bind]; constructor; assumption
    intro y; apply ExtractNonDet.bind <;> solve_by_elim

instance ExtractNonDet.pure' : ExtractNonDet findable (Pure.pure (f := NonDetT m) x) := by
  dsimp [Pure.pure, NonDetT.pure]; constructor

instance ExtractNonDet.liftM (x : m α) :
  ExtractNonDet findable (liftM (n := NonDetT m) x) := by
    dsimp [_root_.liftM, monadLift, MonadLift.monadLift]; constructor
    intro y; apply ExtractNonDet.pure'

instance ExtractNonDet.assume' {p : Prop} : ExtractNonDet findable (MonadNonDet.assume (m :=  NonDetT m) p) := by
  dsimp [MonadNonDet.assume, NonDetT.assume]; apply ExtractNonDet.assume
  intro y; apply ExtractNonDet.pure

instance ExtractNonDet.pickSuchThat' {τ : Type u} (p : τ -> Prop) [Findable p] :
  ExtractNonDet Findable (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) := by
    dsimp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]; constructor
    assumption; intro y; apply ExtractNonDet.pure

instance ExtractNonDet.pickSuchThat_weak {τ : Type u} (p : τ -> Prop) [WeakFindable p] :
  ExtractNonDet WeakFindable (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) := by
    dsimp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]; constructor
    assumption; intro y; apply ExtractNonDet.pure


instance ExtractNonDet.if {p : Prop} {dec : Decidable p} {x y : NonDetT m α}
  (_ : ExtractNonDet findable x) (_ : ExtractNonDet findable y) :
  ExtractNonDet findable (if p then x else y) := by
    match dec with
    | .isTrue h => dsimp [ite]; assumption
    | .isFalse h => dsimp [ite]; assumption

instance ExtractNonDet.ForIn_list {xs : List α} {init : β} {f : α → β → NonDetT m (ForInStep β)}
  (_ : ∀ a b, ExtractNonDet findable (f a b)) :
  ExtractNonDet findable (forIn xs init f) := by
    unhygienic induction xs generalizing init
    { dsimp [forIn]; apply ExtractNonDet.pure }
    { simp only [List.forIn_cons]
      apply ExtractNonDet.bind; solve_by_elim
      rintro (_|_)
      { dsimp; apply ExtractNonDet.pure }
      dsimp; apply tail_ih }


instance ExtractNonDet.forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetT m (ForInStep β)) :
  (∀ b, ExtractNonDet findable (f () b)) ->
  ExtractNonDet findable (forIn Lean.Loop.mk init f) := by
    intro ex
    apply (ExtractNonDet.repeatCont _ _ _ ex); intro;
    apply ExtractNonDet.pure

variable [Monad m] [∀ α, CCPO (m α)] [CCPOBot m] [MonoBind m] [CompleteBooleanAlgebra l] [MPropOrdered m l] [MPropDet m l] [LawfulMonad m]

@[simp, inline]
def NonDetT.extractGen {findable : {τ : Type u} -> (τ -> Prop) -> Type u}
  (findOf : ∀ {τ : Type u} (p : τ -> Prop), findable p -> Option τ)
  : {α : Type u} -> (s : NonDetT m α) -> (ex : ExtractNonDet findable s := by solve_by_elim) -> m α
  | _, .pure x, _ => Pure.pure x
  | _, .vis x f, .vis _ _ _ => liftM x >>= (fun x => extractGen findOf (f x))
  | _, .pickCont _ p f, .pickSuchThat _ _ _ _ =>
    match findOf p ‹_› with
    | none => CCPOBot.compBot
    | some x =>  extractGen findOf (f x)
  | _, .pickCont _ _ f, .assume _ _ _ => extractGen findOf (f .unit)
  | _, .repeatCont init f cont, .repeatCont _ _ _ _ _ =>
    forIn Lean.Loop.mk init (fun _ x => extractGen findOf (f x)) >>= (fun x => extractGen findOf (cont x))

@[inline]
def NonDetT.extract {α : Type u} (s : NonDetT m α) (ex : ExtractNonDet Findable s := by solve_by_elim) : m α :=
  NonDetT.extractGen Findable.find s

def NonDetT.extractWeak {α : Type u} (s : NonDetT m α) (ex : ExtractNonDet WeakFindable s := by solve_by_elim) : m α :=
  NonDetT.extractGen WeakFindable.find s

macro "extract_step" : tactic =>
  `(tactic|
    first
      | eapply ExtractNonDet.forIn
      | eapply ExtractNonDet.ForIn_list
      | eapply ExtractNonDet.bind
      | eapply ExtractNonDet.pure'
      | eapply ExtractNonDet.liftM
      | eapply ExtractNonDet.assume'
      | eapply ExtractNonDet.pickSuchThat'
      | eapply ExtractNonDet.pickSuchThat_weak
      | split)

macro "extract_tactic" : tactic =>
  `(tactic| repeat' (intros; extract_step <;> try dsimp))

@[inline]
def NonDetT.run {α : Type u} (s : NonDetT m α) (ex : ExtractNonDet Findable s := by extract_tactic) : m α :=
  NonDetT.extract s ex

def NonDetT.runWeak {α : Type u} (s : NonDetT m α) (ex : ExtractNonDet WeakFindable s := by extract_tactic) : m α :=
  NonDetT.extractWeak s ex

noncomputable
abbrev NonDetT.prop : {α : Type u} -> (s : NonDetT m α) -> Cont l α
  | _, .pure x => Pure.pure x
  | _, .vis x f => fun post => wlp x fun y => NonDetT.prop (f y) post
  | _, .pickCont _ p f => fun post =>
    (⨅ t, ⌜p t⌝ ⇨ NonDetT.prop (f t) post) ⊓ (⨆ t, ⌜p t⌝)
  | _, .repeatCont _ f cont =>
    fun post => ⌜ ∀ b, ⊤ <= (f b).prop ⊤ ∧ ⊤ <= (cont b).prop post ⌝

structure Extractable (x : NonDetT m α) where
  cond : Cont l α
  prop : ∀ post, cond post <= x.prop post

omit [LawfulMonad m] [(α : Type u) → CCPO (m α)] [MonoBind m] [MPropDet m l] in
lemma NonDetT.prop_bind (x : NonDetT m α) (f : α -> NonDetT m β) :
  (x >>= f).prop = fun post => x.prop (fun a => (f a).prop post) := by
  unhygienic induction x
  { rfl }
  { simp [Bind.bind, NonDetT.bind, NonDetT.prop];
    ext post; congr!; erw [f_ih] }
  { simp [Bind.bind, NonDetT.bind, NonDetT.prop];
    ext post; congr!; erw [f_ih] }
  { simp [Bind.bind, NonDetT.bind, NonDetT.prop];
    ext post; congr!; erw [cont_ih] }

omit [(α : Type u) → CCPO (m α)] [MonoBind m] [MPropDet m l] in
lemma NonDetT.prop_mono (x : NonDetT m α) post post' :
  post <= post' -> x.prop post <= x.prop post' := by
  intro postLe; unhygienic induction x <;> simp only [NonDetT.prop]
  { solve_by_elim }
  { solve_by_elim [wlp_cons] }
  { apply inf_le_inf_right; apply iInf_mono; intro
    aesop }
  apply LE.pure_imp; intro h b; specialize h b
  revert h; simp only [and_imp]; intro h₁ h₂; simp only [h₁, true_and]
  solve_by_elim [le_trans]


def Extractable.bind (x : NonDetT m α) (f : α -> NonDetT m β)
  (ex : Extractable x) (exf : ∀ a, Extractable (f a)) :
  Extractable (x >>= f) := by
    exists fun post => ex.cond (fun a => (exf a).cond post)
    intro post; rw [NonDetT.prop_bind]
    simp [Bind.bind, NonDetT.bind, NonDetT.prop]
    apply le_trans'; apply NonDetT.prop_mono
    { intro a; apply (exf a).prop }
    apply ex.prop

def Extractable.pure (x : α) : Extractable (pure (f := NonDetT m) x) := by
  exists fun post => post x
  intro post; simp [NonDetT.prop, Pure.pure]

def Extractable.liftM (x : m α) : Extractable (liftM (n := NonDetT m) x) := by
  exists wlp x
  intro post; simp [_root_.liftM, NonDetT.prop]; apply wlp_cons; rfl

noncomputable
def Extractable.assume (p : Prop) :
  Extractable (MonadNonDet.assume (m := NonDetT m) p) := by
  exists fun post => ⌜ p ⌝ ⊓ post .unit
  intro post; simp [NonDetT.prop, MonadNonDet.assume, NonDetT.assume, Pure.pure, iSup_const]

noncomputable
def Extractable.pickSuchThat (τ : Type u) (p : τ -> Prop) [Encodable τ] [DecidablePred p] :
  Extractable (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) := by
    exists fun post => (⨅ t, ⌜ p t ⌝ ⇨ post t) ⊓ (⨆ t, ⌜ p t ⌝)
    intro post; simp [NonDetT.prop, MonadNonDet.pickSuchThat, NonDetT.pickSuchThat, Pure.pure, iInf_const]

noncomputable
def Extractable.forIn (xs : List α) (init : β) (f : α -> β -> NonDetT m (ForInStep β))
  (ex: ∀ a b, Extractable (f a b)):
  Extractable (forIn xs init f) := by
    exists fun post => ⌜⊤ <= post ∧ ∀ a b, ⊤ <= (ex a b).cond ⊤⌝
    intro post; dsimp
    by_cases h : (⊤ <= post ∧ ∀ a b, ⊤ <= (ex a b).cond ⊤) = False
    { rw [h]; simp }
    have : (⊤ <= post ∧ ∀ a b, ⊤ <= (ex a b).cond ⊤) = True := by aesop
    simp at h
    rw [this]; simp only [trueE]
    induction xs generalizing init
    { simp [Pure.pure, NonDetT.prop, h] }
    simp only [List.forIn_cons, NonDetT.prop_bind]
    apply le_trans'; apply (ex _ _).prop
    rw [<-h.right]; apply le_of_eq; congr
    ext (_|_)
    { simp [Pure.pure, NonDetT.prop, h] }
    simp_all

noncomputable
def Extractable.forIn_range (m : Type -> Type v) (l : Type) {β : Type} [CompleteBooleanAlgebra l] [Monad m] [MPropOrdered m l] (xs : Std.Range) (init : β) (f : ℕ -> β -> NonDetT m (ForInStep β))
  (ex: ∀ a b, Extractable (f a b)):
  Extractable (ForIn.forIn xs init f) := by
    unfold instForInOfForIn'; simp; solve_by_elim [forIn]

noncomputable
def Extractable.forIn'   (f : Unit -> β -> NonDetT m (ForInStep β))
  (ex : ∀ a, Extractable (f () a)) :
  Extractable (ForIn.forIn Lean.Loop.mk init f) := by
    exists fun post => ⌜⊤ <= post ∧ ∀ a, ⊤ <= (ex a).cond ⊤⌝
    simp [ForIn.forIn, NonDetT.prop, rep, NonDetT.repeat, Pure.pure]
    intro posth
    have h : ∀ (b : β), (f () b).prop ⊤ = ⊤ := by {
      intro b; refine eq_top_iff.mpr ?_
      apply le_trans'; apply (ex b).prop; simp
      simp [posth] }
    simp [h]

noncomputable
def Extractable.if_some {τ} {p : τ -> Prop}
  [Encodable τ]
  [DecidablePred p]
  {dec : Decidable $ ∃ x, p x} {x : τ -> NonDetT m α} {y : NonDetT m α}
  (_ : ∀ t, Extractable (x t)) (_ : Extractable y) :
  Extractable (if ∃ x, p x then MonadNonDet.pickSuchThat τ p >>= x else y) := by
    split_ifs with h
    { apply Extractable.bind
      { exists fun post => (⨅ t, ⌜ p t ⌝ ⇨ post t)
        intro post; simp [MonadNonDet.pickSuchThat, NonDetT.prop, NonDetT.pickSuchThat, Pure.pure]
        rcases h with ⟨t, h⟩
        refine le_iSup_of_le t ?_; simp [h] }
      apply_assumption }
    apply_assumption


omit [LawfulMonad m] [MPropDet m l] [(α : Type u) → CCPO (m α)] [MonoBind m]in
lemma Extractable.intro (x : NonDetT m α) (ex : Extractable x) :
  pre <= ex.cond post ->
  pre <= x.prop post := by
    solve_by_elim [ex.prop, le_trans']



macro "extractable_step" : tactic =>
  `(tactic|
    first
      | eapply Extractable.if_some
      | eapply Extractable.forIn
      | eapply Extractable.bind
      | eapply Extractable.pure
      | eapply Extractable.liftM
      | eapply Extractable.assume
      | eapply Extractable.pickSuchThat)

macro "extractable_tactic" : tactic =>
  `(tactic| repeat' (intros; extractable_step; try dsimp))

namespace TotalCorrectness.DemonicChoice

lemma NonDetDevT.extract_refines_wp (s : NonDetT m α) (inst : ExtractNonDet Findable s) :
  wp s post ⊓ s.prop ⊤ <= wp s.extract post := by
  unhygienic induction inst
  { simp [wp_pure, NonDetT.extract] }
  { simp [NonDetT.wp_vis, NonDetT.prop]; rw [inf_comm, wlp_join_wp]
    simp [NonDetT.extract, wp_bind, ExceptT.wp_lift]
    apply wp_cons; aesop (add norm inf_comm) }
  { simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extract]; split
    { have := Findable.find_none (p := p) (by simpa);
      have : (∀ x, p x = False) := by simpa
      simp [this] }
    rw [<-inf_assoc]; refine inf_le_of_left_le ?_
    rw [← @iInf_inf_eq]; simp [meet_himp _ _ _ _ rfl]
    rename_i y _
    refine iInf_le_of_le y ?_
    have := Findable.find_some_p (p := p) (by assumption)
    simp [this]; apply a_ih }
  { simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extract]
    have: ∀ a : PUnit.{u_1 + 1}, a = .unit := by aesop
    simp [this, iInf_const, iSup_const]; apply le_trans'; apply a_ih
    simp; constructor
    { rw [<-inf_assoc, <-le_himp_iff]; exact inf_le_left }
    refine inf_le_of_right_le ?_; exact inf_le_left }
  rw [NonDetT.wp_repeatCont, NonDetT.extract, NonDetT.extractGen, wp_bind, NonDetT.prop]
  simp; intro hprop inv wf hinv; apply le_trans'; apply wp_cons; rotate_right
  { apply (triple_spec ..).mpr; apply repeat_inv
    intro b; apply le_trans'; apply a_ih; simp [hprop]
    simp [NonDetT.wp_eq_wp, hinv]
    apply hinv }
  intro b; apply le_trans'; apply a_ih_1; simp [hprop]
  simp [NonDetT.wp_eq_wp]

lemma NonDetDevT.extract_refines (pre : l) (s : NonDetT m α) (inst : ExtractNonDet Findable s) :
  triple pre s post ->
  pre <= s.prop ⊤ ->
  triple pre s.extract post := by
  intro tr imp; apply le_trans'; apply NonDetDevT.extract_refines_wp
  simp; aesop

end TotalCorrectness.DemonicChoice

noncomputable
abbrev _root_.NonDetT.prop_part : {α : Type u} -> (s : NonDetT m α) -> Cont l α
  | _, .pure x => Pure.pure x
  | _, .vis x f => fun post => wlp x fun y => NonDetT.prop (f y) post
  | _, .pickCont _ p f => fun post =>
    (⨅ t, ⌜p t⌝ ⇨ NonDetT.prop (f t) post)
  | _, .repeatCont _ f cont =>
    fun post => ⌜ ∀ b, ⊤ <= (f b).prop ⊤ ∧ ⊤ <= (cont b).prop post ⌝

namespace PartialCorrectness.DemonicChoice

variable [MPropPartial m]


lemma NonDetDevT.extract_refines_wp (s : NonDetT m α) (inst : ExtractNonDet WeakFindable s) :
  wp s post ⊓ s.prop ⊤ <= wp s.extractWeak post := by
  unhygienic induction inst
  { simp [wp_pure, NonDetT.extractWeak] }
  { simp [NonDetT.wp_vis, NonDetT.prop]; rw [inf_comm, wlp_join_wp]
    simp [NonDetT.extractWeak, wp_bind, ExceptT.wp_lift]
    apply wp_cons; aesop (add norm inf_comm) }
  { simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extractWeak]; split
    simp [CCPOBot.prop, wp_bot]
    rw [<-inf_assoc]; refine inf_le_of_left_le ?_
    rw [← @iInf_inf_eq]; simp [meet_himp _ _ _ _ rfl]
    rename_i y _
    refine iInf_le_of_le y ?_
    have := WeakFindable.find_some_p (p := p) (by assumption)
    simp [this]; apply a_ih }
  { simp [NonDetT.wp_pickCont, NonDetT.prop, NonDetT.extractWeak]
    have: ∀ a : PUnit.{u_1 + 1}, a = .unit := by aesop
    simp [this, iInf_const, iSup_const]; apply le_trans'; apply a_ih
    simp; constructor
    { rw [<-inf_assoc, <-le_himp_iff]; exact inf_le_left }
    refine inf_le_of_right_le ?_; exact inf_le_left }
  rw [NonDetT.wp_repeatCont, NonDetT.extractWeak, NonDetT.extractGen, wp_bind, NonDetT.prop]
  simp; intro hprop inv hinv; apply le_trans'; apply wp_cons; rotate_right
  { apply (triple_spec ..).mpr; apply repeat_inv
    intro b; apply le_trans'; apply a_ih; simp [hprop]
    simp [NonDetT.wp_eq_wp, hinv] }
  intro b; apply le_trans'; apply a_ih_1; simp [hprop]
  simp [NonDetT.wp_eq_wp]

lemma NonDetDevT.extract_refines (pre : l) (s : NonDetT m α) (inst : ExtractNonDet WeakFindable s) :
  triple pre s post ->
  pre <= s.prop ⊤ ->
  triple pre s.extractWeak post := by
  intro tr imp; apply le_trans'; apply NonDetDevT.extract_refines_wp
  simp; aesop

end PartialCorrectness.DemonicChoice
