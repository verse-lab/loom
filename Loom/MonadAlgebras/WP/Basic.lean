import Loom.MonadAlgebras.Defs

import Loom.MonadAlgebras.Instances.Basic
import Loom.MonadAlgebras.Instances.ExceptT
import Loom.MonadAlgebras.Instances.StateT
import Loom.MonadAlgebras.Instances.ReaderT

universe u v w

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u}

section
variable [CompleteLattice l]
section
variable [mprop : MPropOrdered m l]

def wp (c : m α) (post : α -> l) : l := liftM (n := Cont l) c post
def triple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ≤ wp c post

lemma wp_pure (x : α) (post : α -> l) : wp (m := m) (pure x) post = post x := by
  simp [wp, liftM, lift_pure]
  rfl

lemma triple_pure (pre : l) (x : α) (post : α -> l) :
  triple pre (pure (f := m) x) post <-> pre ≤ (post x)
  := by
    rw [triple, wp]; simp [liftM, lift_pure]; rfl

end

variable [MPropOrdered m l]

lemma wp_bind {β} (x : m α) (f : α -> m β) (post : β -> l) :
    wp (x >>= f) post = wp x (fun x => wp (f x) post) := by
    simp [wp, liftM]; rw [lift_bind]; rfl

lemma wp_cons (x : m α) (post post' : α -> l) :
  (∀ y, post y ≤ post' y) ->
  wp x post ≤ wp x post' := by
    intros h; simp [wp, liftM, monadLift]; apply Cont.monotone_lift; intros y
    apply h

lemma triple_bind {β} (pre : l) (x : m α) (cut : α -> l)
  (f : α -> m β) (post : β -> l) :
  triple pre x cut ->
  (∀ y, triple (cut y) (f y) post) ->
  triple pre (x >>= f) post := by
    intros; simp [triple, wp_bind]
    solve_by_elim [le_trans', wp_cons]

omit [LawfulMonad m] in
@[simp]
lemma wp_top (c : m α) [NoFailure m] :
  wp c (fun _ => ⊤) = ⊤ := by
    simp [wp, liftM, monadLift, NoFailure.noFailure]

end

section
variable [CompleteLattice l] [MPropOrdered m l]

noncomputable
def spec (pre : l) (post : α -> l) : Cont l α :=
  fun p => pre ⊓ ⌜post ≤ p⌝

lemma triple_spec (pre : l) (c : m α) (post : α -> l) :
  spec pre post <= wp c <->
  triple pre c post := by
    constructor
    { intro h; unfold triple
      specialize h post; apply le_trans'; apply h
      unfold spec; simp [trueE] }
    intro t p; unfold spec
    by_cases h: post ≤ p
    { apply inf_le_of_left_le; apply le_trans; apply t
      solve_by_elim [Cont.monotone_lift (x := c)] }
    have : (post ≤ p) = False := by simp [h]
    simp [this, falseE]

end

section Determenism

variable [inst: CompleteLattice l] [MPropOrdered m l]

lemma wp_iInf {ι : Type u} [Nonempty ι] [MPropDet m l] (c : m α) (post : ι -> α -> l) :
  wp c (fun x => ⨅ i, post i x) = ⨅ i, wp c (post i) := by
    apply le_antisymm
    { refine le_iInf ?_; intros i; apply wp_cons; intro y
      exact iInf_le (fun i ↦ post i y) i }
    apply MPropDet.demonic

lemma wp_and [MPropDet m l] (c : m α) (post₁ post₂ : α -> l) :
  wp c (fun x => post₁ x ⊓ post₂ x) = wp c post₁ ⊓ wp c post₂ := by
  apply le_antisymm
  { simp; constructor <;> apply wp_cons <;> simp }
  have h := MPropDet.demonic (l := l) (ι := ULift Bool) (c := c) (p := fun | .up true => post₁ | .up false => post₂)
  simp at h
  apply le_trans; apply le_trans'; apply h
  { simp [wp]; constructor; exact inf_le_right
    exact inf_le_left }
  apply wp_cons (m := m); simp; intros; constructor
  { refine iInf_le_of_le true ?_; simp }
  refine iInf_le_of_le false ?_; simp

lemma wp_iSup {ι : Type u} [Nonempty ι] [MPropDet m l] (c : m α) (post : ι -> α -> l) :
  wp c (fun x => ⨆ i, post i x) = ⨆ i, wp c (post i) := by
    apply le_antisymm
    { apply MPropDet.angelic }
    refine iSup_le ?_; intros i; apply wp_cons; intro y
    exact le_iSup (fun i ↦ post i y) i


lemma wp_or [MPropDet m l] (c : m α) (post₁ post₂ : α -> l) :
  wp c (fun x => post₁ x ⊔ post₂ x) = wp c post₁ ⊔ wp c post₂ := by
  apply le_antisymm
  { have h := MPropDet.angelic (l := l) (ι := ULift Bool) (c := c) (p := fun | .up true => post₁ | .up false => post₂)
    simp [-iSup_le_iff] at h
    apply le_trans; apply le_trans'; apply h
    { apply wp_cons (m := m); simp; intros; constructor
      { refine le_iSup_of_le true ?_; simp }
      refine le_iSup_of_le false ?_; simp }
    simp [wp]; constructor; exact le_sup_right
    exact le_sup_left }
  simp; constructor <;> apply wp_cons <;> simp


end Determenism


section Loops

open Lean.Order

@[specialize, inline]
def Loop.forIn.loop {m : Type u -> Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m] (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop f b
  partial_fixpoint

@[inline]
def Loop.forIn {β : Type u} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
  (_ : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  Loop.forIn.loop f init

@[instance high]
instance [md : Monad m] [ccpo : ∀ α, CCPO (m α)] [mono : MonoBind m] : ForIn m Lean.Loop Unit where
  forIn {β} _ := @Loop.forIn m β md ccpo mono

variable [inst: _root_.CompleteLattice l] [MPropOrdered m l]

namespace PartialCorrectness

variable [∀ α, CCPO (m α)] [MonoBind m] [MPropPartial m]

omit [MonoBind m] [LawfulMonad m] in
lemma wp_csup (xc : Set (m α)) (post : α -> l) :
  Lean.Order.chain xc ->
  ⨅ c ∈ xc, wp c post ≤ wp (Lean.Order.CCPO.csup xc) post := by
  apply MPropPartial.csup_lift

omit [MonoBind m] [LawfulMonad m] in
lemma wp_bot :
  wp (bot : m α) = fun _ => (⊤ : l) := by
  ext post; refine eq_top_iff.mpr ?_
  apply le_trans'; apply wp_csup; simp [chain]
  refine le_iInf₂ ?_
  intro; erw [Set.mem_empty_iff_false]; simp

lemma repeat_inv (f : Unit -> β -> m (ForInStep β))
  (inv : ForInStep β -> l)
  init :
   (∀ b, triple (inv (.yield b)) (f () b) (inv)) ->
   triple (inv (.yield init)) (Loop.forIn.loop f init) (fun b => inv (.done b)) := by
  intro hstep
  revert init
  apply Loop.forIn.loop.fixpoint_induct (f := f) (motive :=
    fun loop => ∀ init, triple (inv (.yield init)) (loop init) (fun b =>inv (.done b)))
  { apply Lean.Order.admissible_pi_apply
      (P := fun init loop => triple (inv (.yield init)) (loop) (fun b =>inv (.done b)))
    simp [admissible, triple]; intro init loops cl h
    apply le_trans'; apply wp_csup; solve_by_elim
    simp; solve_by_elim }
  intro loop ih init; simp [triple, wp_bind]; apply le_trans; apply hstep
  apply wp_cons; rintro (_|_); simp [wp_pure]
  apply ih

lemma repeat_inv_split (f : Unit -> β -> m (ForInStep β))
  (inv : β -> l) (doneWith : β -> l)
  init :
   (∀ b, triple (inv b) (f () b) (fun | .yield b' => inv b' | .done b' => inv b' ⊓ doneWith b')) ->
   triple (inv init) (Loop.forIn.loop f init) (fun b => inv b ⊓ doneWith b) := by
  intro hstep
  apply repeat_inv f (fun | .yield b => inv b | .done b => inv b ⊓ doneWith b) init
  apply hstep

end PartialCorrectness

namespace TotalCorrectness

variable [∀ α, CCPO (m α)] [MonoBind m]

lemma repeat_inv (f : Unit -> β -> m (ForInStep β)) [WellFoundedRelation β]
  (inv : ForInStep β -> l)
  init :
   (∀ b, triple (inv (.yield b)) (f () b) (fun | .yield b' => inv (.yield b') ⊓ ⌜ WellFoundedRelation.rel b' b ⌝ | .done b' => inv (.done b'))) ->
   triple (inv (.yield init)) (Loop.forIn.loop f init) (fun b => inv (.done b)) := by
  intro hstep
  apply WellFounded.induction (r := WellFoundedRelation.rel)
    (C := fun init => triple (inv (.yield init)) (Loop.forIn.loop f ( init)) (fun b => inv (.done b)))
  { apply WellFoundedRelation.wf }
  intro b ih; unfold Loop.forIn.loop; simp [triple, wp_bind]; apply le_trans
  apply hstep; apply wp_cons; rintro (_|_) <;> simp [wp_pure]
  solve_by_elim


lemma repeat_inv_split (f : Unit -> β -> m (ForInStep β)) [WellFoundedRelation β]
  (inv : β -> l) (doneWith : β -> l)
  init :
    (∀ b, triple (inv b) (f () b) (fun | .yield b' => inv b' ⊓ ⌜ WellFoundedRelation.rel b' b ⌝ | .done b' => inv b' ⊓ doneWith b')) ->
    triple (inv init) (Loop.forIn.loop f init) (fun b => inv b ⊓ doneWith b) := by
  intro hstep
  apply repeat_inv f (fun | .yield b => inv b | .done b => inv b ⊓ doneWith b) init
  apply hstep

variable [MPropTotal m]

omit [LawfulMonad m] [MonoBind m] in
attribute [-simp] le_bot_iff in
@[simp]
lemma wp_bot :
  wp (bot : m α) = fun _ => (⊥ : l) := by
  ext post; refine eq_bot_iff.mpr ?_
  simp [wp, liftM, monadLift]; apply  MPropTotal.bot_lift

end TotalCorrectness

theorem triple_forIn_list {α β}
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : List α → β → l)
  (hstep : ∀ hd tl b,
    triple
      (inv (hd :: tl) b)
      (f hd b)
      (fun | .yield b' => inv tl b' | .done b' => inv [] b')) :
  triple (inv xs init) (forIn xs init f) (inv []) := by
    induction xs generalizing init
    { simp; rw [triple_pure] }
    simp only [List.forIn_cons]
    apply triple_bind; apply hstep; intros y
    cases y <;> simp <;> solve_by_elim [(triple_pure ..).mpr, le_refl]

theorem triple_forIn_range'_aux {β}
  {xstart : ℕ} {step : ℕ} (n : ℕ) (init : β) {f : ℕ → β → m (ForInStep β)}
  (inv : ℕ → β → l)
  (hstep : ∀ i b,
    triple
      (inv i b)
      (f i b)
      (fun | .yield b' => inv (i + step) b' | .done b' => inv (xstart + n * step) b')) :
  i <= n ->
  triple (inv (xstart + (n - i) * step) init) (forIn (List.range' (xstart + (n - i) * step) i step) init f) (inv (xstart + n * step)) := by
  unhygienic induction i generalizing init
  { simp [triple_pure] }
  intro le
  simp [List.range']; apply triple_bind; apply hstep
  rintro (_|_) <;> simp [triple_pure]
  simp [Nat.add_assoc, <-Nat.add_one_mul]
  have : (n - (n_1 + 1) + 1) = n - n_1 := by omega
  rw [this]; apply a; omega


theorem triple_forIn_range' {β}
  {xstart : ℕ} {step : ℕ} (n : ℕ) {init : β} {f : ℕ → β → m (ForInStep β)}
  (inv : ℕ → β → l)
  (hstep : ∀ i b,
    triple
      (inv i b)
      (f i b)
      (fun | .yield b' => inv (i + step) b' | .done b' => inv (xstart + n * step) b')) :
  triple (inv xstart init) (forIn (List.range' xstart n step) init f) (inv (xstart + n * step)) := by
    have := triple_forIn_range'_aux (i := n) (m := m) n init inv hstep (by omega)
    simp_all only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]

theorem triple_forIn_range {β}
  (xs : Std.Range) (init : β) (f : ℕ → β → m (ForInStep β))
  (inv : ℕ → β → l)
  (hstep : ∀ i b,
    triple
      (inv i b)
      (f i b)
      (fun | .yield b' => inv (i + xs.step) b' | .done b' => inv (xs.start + ((xs.stop - xs.start + xs.step - 1) / xs.step) * xs.step) b')) :
  triple (inv xs.start init) (forIn xs init f) (inv (xs.start + ((xs.stop - xs.start + xs.step - 1) / xs.step) * xs.step)) := by
  simp; apply triple_forIn_range'; apply hstep

theorem triple_forIn_range_step1 {β}
  {xs : Std.Range} {init : β} {f : ℕ → β → m (ForInStep β)}
  (inv : ℕ → β → l)
  (hstep : ∀ i b,
    triple
      (inv i b)
      (f i b)
      (fun | .yield b' => inv (i + xs.step) b' | .done b' => inv xs.stop b')) :
  xs.step = 1 ->
  xs.start <= xs.stop ->
  triple (inv xs.start init) (forIn xs init f) (inv xs.stop) := by
  have := triple_forIn_range (m := m)  xs init f inv
  intro h eq;
  simp [h] at *
  rw [Nat.add_sub_of_le eq] at this;
  solve_by_elim

end Loops


section Lift

variable [inst: CompleteLattice l] [MPropOrdered m l]

lemma wp_except_handler_eq ε (hd : ε -> Prop) [IsHandler hd] (c : ExceptT ε m α) post :
  wp c post = wp (m := m) c (fun | .ok x => post x | .error e => ⌜hd e⌝) := by
    apply MProp.lift_ExceptT


open ExceptionAsSuccess in
lemma wp_part_eq ε (c : ExceptT ε m α) post :
  wp c post = wp (m := m) c (fun | .ok x => post x | .error _ => ⊤) := by
    simp [wp_except_handler_eq]

open ExceptionAsFailure in
lemma wp_tot_eq ε (c : ExceptT ε m α) post :
  wp c post = wp (m := m) c (fun | .ok x => post x | .error _ => ⊥) := by
    simp [wp_except_handler_eq]


lemma ExceptT.wp_lift_hd {hd : ε -> Prop} (c : m α) (post : α -> l) [IsHandler hd] :
  wp (liftM (n := ExceptT ε m) c) post = wp (m := m) c post := by
  simp [wp_except_handler_eq, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, mk]
  rw [map_eq_pure_bind, wp_bind]; simp [wp_pure]

lemma ExceptionAsSuccess.ExceptT.wp_lift (c : m α) (post : α -> l) :
  wp (liftM (n := ExceptT ε m) c) post = wp (m := m) c post := by
  apply ExceptT.wp_lift_hd

lemma ExceptionAsFailure.ExceptT.wp_lift (c : m α) (post : α -> l) :
  wp (liftM (n := ExceptT ε m) c) post = wp (m := m) c post := by
  apply ExceptT.wp_lift_hd

open TotalCorrectness in
lemma TotalCorrectness.DivM.wp_eq (α : Type) (x : DivM α) (post : α -> Prop) :
  wp x post =
    match x with
    | .div => False
    | .res r => post r := by
  simp [wp, liftM, monadLift, MProp.lift, Functor.map, TotalCorrectness.instMPropOrderedDivMProp]
  cases x <;> simp [LE.pure]

lemma PartialCorrectness.DivM.wp_eq (α : Type) (x : DivM α) (post : α -> Prop) :
  wp x post =
    match x with
    | .div => True
    | .res r => post r := by
  simp [wp, liftM, monadLift, MProp.lift, Functor.map, PartialCorrectness.instMPropOrderedDivMProp]
  cases x <;> simp [LE.pure]

lemma StateT.wp_eq (c : StateT σ m α) (post : α -> σ -> l) :
  wp c post = fun s => wp (m := m) (c s) (fun xs => post xs.1 xs.2) := by
  simp [wp, liftM, monadLift, MProp.lift_StateT, MonadLift.monadLift, StateT.lift];

lemma StateT.wp_lift (c : m α) (post : α -> σ -> l) :
  wp (liftM (n := StateT σ m) c) post = fun s => wp (m := m) c (post · s) := by
  simp [wp, liftM, monadLift, MProp.lift_StateT, MonadLift.monadLift, StateT.lift];
  have liftE : ∀ α, MProp.lift (m := m) (α := α) = wp := by intros; ext; simp [wp, liftM, monadLift]
  ext s; rw [map_eq_pure_bind, liftE, liftE, wp_bind]; simp [wp_pure]

lemma ReaderT.wp_eq (c : ReaderT σ m α) (post : α -> σ -> l) :
  wp c post = fun s => wp (m := m) (c s) (post · s) := by
  simp [wp, liftM, monadLift, MProp.lift_ReaderT, MonadLift.monadLift];

lemma ReaderT.wp_lift (c : m α) (post : α -> σ -> l) :
  wp (liftM (n := ReaderT σ m) c) post = fun s => wp (m := m) c (post · s) := by
  simp [wp, liftM, monadLift, MProp.lift_ReaderT, MonadLift.monadLift, StateT.lift]

end Lift

-- section StrongestPostcondition

-- variable [inst: CompleteLattice l] [MPropOrdered m l]

-- def sp (x : m α) (pre : l) : α -> l := (sInf fun post => pre <= wp x post)

-- lemma le_wp_sp_le (x : m α) [LawfulMonad m] [MPropDet m l] :
--   post ≠ ⊤ ->
--    (sp x pre <= post -> pre <= wp x post) := by
--     intro pne
--     by_cases ex:  Nonempty (Set.Elem fun post ↦ pre ≤ wp x post)
--     { have : pre <= wp x (sp x pre) := by {
--         unfold sp; simp [sInf]; rw [@wp_iInf]
--         revert ex; simp [Set.Elem, Set.Mem, Membership.mem] }
--       solve_by_elim [wp_cons, le_trans] }
--     rw [@Set.not_nonempty_iff_eq_empty'] at ex
--     simp [sp, ex, *]

-- lemma sp_le_le_wp (x : m α) :
--    (pre <= wp x post -> sp x pre <= post) := by
--     intro a; --refine inf_le_of_left_le ?_
--     exact CompleteSemilatticeInf.sInf_le (fun post ↦ pre ≤ wp x post) post a


-- end StrongestPostcondition
