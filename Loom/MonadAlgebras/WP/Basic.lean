import Loom.MonadAlgebras.Defs

import Loom.MonadAlgebras.Instances.Basic
import Loom.MonadAlgebras.Instances.ExceptT
import Loom.MonadAlgebras.Instances.StateT
import Loom.MonadAlgebras.Instances.ReaderT

open Loom Loom.Order

universe u v w

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u}

section
variable [CompleteLattice l]
section
variable [mprop : MAlgOrdered m l]

/- WP definition -/
def wp (c : m α) (post : α -> l) : l := liftM (n := Cont l) c post
/- Hoare triple definition -/
def triple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ⊑ₗ wp c post

/- WP of pure (defintion 4 from the paper) -/
theorem wp_pure (x : α) (post : α -> l) : wp (m := m) (pure x) post = post x := by
  simp [wp, liftM]
  rfl

/- WP of bind (defintion 5 from the paper) -/
theorem triple_pure (pre : l) (x : α) (post : α -> l) :
  triple pre (pure (f := m) x) post <-> pre ⊑ₗ (post x)
  := by
    rw [triple, wp]; simp [liftM]; rfl

end

variable [MAlgOrdered m l]

theorem wp_bind {β} (x : m α) (f : α -> m β) (post : β -> l) :
    wp (x >>= f) post = wp x (fun x => wp (f x) post) := by
    simp [wp, liftM]; rfl

theorem wp_map {β} (x : m α) (f : α -> β) (post : β -> l) :
  wp (f <$> x) post = wp x (fun x => post (f x)) := by
    rw [map_eq_pure_bind, wp_bind]; simp [wp_pure]

/- monotonicity for WP (definition 9 from the paper) -/
theorem wp_cons (x : m α) (post post' : α -> l) :
  (∀ y, post y ⊑ₗ post' y) ->
  wp x post ⊑ₗ wp x post' := by
    intros h; simp [wp, liftM, monadLift]; apply Cont.monotone_lift; intros y
    apply h

theorem triple_cons (x : m α) {pre pre' : l} {post post' : α -> l} :
  pre' ⊑ₗ pre ->
  (∀ y, post y ⊑ₗ post' y) ->
  triple pre x post ->
  triple pre' x post' := by
    intros hpre hpost h
    apply le_trans'; apply wp_cons; apply hpost
    solve_by_elim [le_trans]

theorem triple_bind {β} (pre : l) (x : m α) (cut : α -> l)
  (f : α -> m β) (post : β -> l) :
  triple pre x cut ->
  (∀ y, triple (cut y) (f y) post) ->
  triple pre (x >>= f) post := by
    intros; simp [triple, wp_bind]
    solve_by_elim [le_trans', wp_cons]

omit [LawfulMonad m] in
@[simp]
theorem wp_top (c : m α) [NoFailure m] :
  wp c (fun _ => ⊤ₗ) = ⊤ₗ := by
    simp [wp, liftM, monadLift] ; apply NoFailure.noFailure

end

section
variable [CompleteLattice l] [MAlgOrdered m l]

noncomputable
def spec (pre : l) (post : α -> l) : Cont l α :=
  fun p => pre ⊓ₗ ⌜post ⊑ₗ p⌝

theorem triple_spec (pre : l) (c : m α) (post : α -> l) :
  spec pre post ⊑ₗ wp c <->
  triple pre c post := by
    constructor
    { intro h; unfold triple
      specialize h post; apply le_trans'; apply h
      unfold spec; simp [trueE] }
    intro t p; unfold spec
    by_cases h: post ⊑ₗ p
    { apply inf_le_of_left_le; apply le_trans; apply t
      solve_by_elim [Cont.monotone_lift (x := c)] }
    have : (post ⊑ₗ p) = False := by simp [h]
    simp [this, falseE]

end

section Determinism

variable [inst: CompleteLattice l] [MAlgOrdered m l]

theorem wp_iInf {ι : Type u} [Nonempty ι] [MAlgDet m l] (c : m α) (post : ι -> α -> l) :
  wp c (fun x => ⨅ₗ i, post i x) = ⨅ₗ i, wp c (post i) := by
    apply le_antisymm
    { refine le_iInf ?_; intros i; apply wp_cons; intro y
      exact iInf_le (fun i ↦ post i y) i }
    apply MAlgDet.demonic

theorem wp_and [MAlgDet m l] (c : m α) (post₁ post₂ : α -> l) :
  wp c (fun x => post₁ x ⊓ₗ post₂ x) = wp c post₁ ⊓ₗ wp c post₂ := by
  have h := wp_iInf (ι := ULift Bool) c
    (fun | .up false => post₁ | .up true => post₂)
  simpa using h


theorem wp_iSup {ι : Type u} [Nonempty ι] [MAlgDet m l] (c : m α) (post : ι -> α -> l) :
  wp c (fun x => ⨆ₗ i, post i x) = ⨆ₗ i, wp c (post i) := by
    apply le_antisymm
    { apply MAlgDet.angelic }
    refine iSup_le ?_; intros i; apply wp_cons; intro y
    exact le_iSup (fun i ↦ post i y) i


theorem wp_or [MAlgDet m l] (c : m α) (post₁ post₂ : α -> l) :
  wp c (fun x => post₁ x ⊔ₗ post₂ x) = wp c post₁ ⊔ₗ wp c post₂ := by
  have h := wp_iSup (ι := ULift Bool) c
    (fun | .up false => post₁ | .up true => post₂)
  simpa using h


end Determinism


section Loops

open Lean.Order

/- partial loop from MonoBind and CCPO instances -/
@[specialize, inline]
def Loop.forIn.loop {m : Type u -> Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m] (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop f b
  partial_fixpoint

@[inline]
def Loop.forIn {β : Type u} [∀ α, CCPO (m α)] [MonoBind m]
  (_ : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  Loop.forIn.loop f init

-- @[instance high]
-- instance [md : Monad m] [ccpo : ∀ α, CCPO (m α)] [mono : MonoBind m] : ForIn m Lean.Loop Unit where
--   forIn {β} _ := @Loop.forIn m β md ccpo mono

variable [inst: Loom.Order.CompleteLattice l] [MAlgOrdered m l]

namespace PartialCorrectness

variable [∀ α, CCPO (m α)] [MonoBind m] [MAlgPartial m]

-- omit [MonoBind m] [LawfulMonad m] in
-- theorem wp_csup (xc : Set (m α)) (post : α -> l) :
--   Lean.Order.chain xc ->
--   ⨅ₗ c ∈ xc, wp c post ⊑ₗ wp (Lean.Order.CCPO.csup xc) post := by
--   apply MAlgPartial.csup_lift

-- omit [MonoBind m] [LawfulMonad m] in
-- theorem wp_bot :
--   wp (bot : m α) = fun _ => (⊤ₗ : l) := by
--   ext post; refine eq_top_iff.mpr ?_
--   apply le_trans'; apply wp_csup; simp [chain]
--   refine le_iInf₂ ?_
--   intro; erw [Set.mem_empty_iff_false]; simp

-- theorem repeat_inv (f : Unit -> β -> m (ForInStep β))
--   (inv : ForInStep β -> l)
--   init :
--    (∀ b, triple (inv (.yield b)) (f () b) (inv)) ->
--    triple (inv (.yield init)) (Loop.forIn.loop f init) (fun b => inv (.done b)) := by
--   intro hstep
--   revert init
--   apply Loop.forIn.loop.fixpoint_induct (f := f) (motive :=
--     fun loop => ∀ init, triple (inv (.yield init)) (loop init) (fun b =>inv (.done b)))
--   { apply Lean.Order.admissible_pi_apply
--       (P := fun init loop => triple (inv (.yield init)) (loop) (fun b =>inv (.done b)))
--     simp [admissible, triple]; intro init loops cl h
--     apply le_trans'; apply wp_csup; solve_by_elim
--     simp; solve_by_elim }
--   intro loop ih init; simp [triple, wp_bind]; apply le_trans; apply hstep
--   apply wp_cons; rintro (_|_); simp [wp_pure]
--   apply ih

-- theorem repeat_inv_split (f : Unit -> β -> m (ForInStep β))
--   (inv : β -> l) (doneWith : β -> l)
--   init :
--    (∀ b, triple (inv b) (f () b) (fun | .yield b' => inv b' | .done b' => inv b' ⊓ₗ doneWith b')) ->
--    triple (inv init) (Loop.forIn.loop f init) (fun b => inv b ⊓ₗ doneWith b) := by
--   intro hstep
--   apply repeat_inv f (fun | .yield b => inv b | .done b => inv b ⊓ₗ doneWith b) init
--   apply hstep

end PartialCorrectness

namespace TotalCorrectness

variable [∀ α, CCPO (m α)] [MonoBind m]

theorem repeat_inv (f : Unit -> β -> m (ForInStep β))
  (inv : ForInStep β -> l) (measure : β -> Nat)
  init :
   (∀ b, triple (inv (.yield b)) (f () b) (fun | .yield b' => inv (.yield b') ⊓ₗ ⌜ measure b' < measure b ⌝ | .done b' => inv (.done b'))) ->
   triple (inv (.yield init)) (Loop.forIn.loop f init) (fun b => inv (.done b)) := by
  intro hstep
  have induc (C : β → Prop) (a : β) (h : ∀ x, (∀ y, measure y < measure x → C y) → C x): C a := by
    have lem: ∀ n: Nat, ∀ x, measure x ≤ n →  C x := by
      intro n
      induction n with
      | zero =>
        intro x hx
        exact h x (fun y => by omega)
      | succ m ih =>
        intro x hx
        by_cases neq: measure x ≤ m
        { exact ih x neq }
        have eq: measure x = m + 1 := by omega
        exact h x (fun y hy => ih y (by omega))
    exact lem (measure a) a (by simp)
  apply induc
    (fun ini => triple (inv (.yield ini)) (Loop.forIn.loop f ( ini)) (fun b => inv (.done b))) init
  intro b ih; unfold Loop.forIn.loop; simp [triple, wp_bind]; apply le_trans
  apply hstep; apply wp_cons; rintro (_|_)
  { simp [wp_pure] }
  rename_i a
  match ForInStep.yield a with
  | .yield b' =>
    simp; intro m_lt
    have ihb := ih b' m_lt
    simp [triple] at ihb
    exact ihb
  | .done b' =>
    simp
    rw [wp_pure b' (fun s: β => inv (ForInStep.done s))]


theorem repeat_inv_split (f : Unit -> β -> m (ForInStep β))
  (inv : β -> l) (doneWith : β -> l)
  init  (measure: β -> Nat):
    (∀ b, triple (inv b) (f () b) (fun | .yield b' => inv b' ⊓ₗ ⌜ measure b' < measure b ⌝ | .done b' => inv b' ⊓ₗ doneWith b')) ->
    triple (inv init) (Loop.forIn.loop f init) (fun b => inv b ⊓ₗ doneWith b) := by
  intro hstep
  apply repeat_inv f (fun | .yield b => inv b | .done b => inv b ⊓ₗ doneWith b) measure init
  apply hstep

variable [MAlgTotal m]

omit [LawfulMonad m] [MonoBind m] in
attribute [-simp] le_bot_iff in
@[simp]
theorem wp_bot :
  wp (bot : m α) = fun _ => (⊥ₗ : l) := by
  ext post; refine eq_bot_iff.mpr ?_
  simp [wp, liftM, monadLift]; apply  MAlgTotal.bot_lift

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
  {xstart : Nat} {step : Nat} (n : Nat) (init : β) {f : Nat → β → m (ForInStep β)}
  (inv : Nat → β → l)
  (hstep : ∀ i b,
    triple
      (inv i b)
      (f i b)
      (fun | .yield b' => inv (i + step) b' | .done b' => inv (xstart + n * step) b')) :
  i ≤ n ->
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
  {xstart : Nat} {step : Nat} (n : Nat) {init : β} {f : Nat → β → m (ForInStep β)}
  (inv : Nat → β → l)
  (hstep : ∀ i b,
    triple
      (inv i b)
      (f i b)
      (fun | .yield b' => inv (i + step) b' | .done b' => inv (xstart + n * step) b')) :
  triple (inv xstart init) (forIn (List.range' xstart n step) init f) (inv (xstart + n * step)) := by
    have := triple_forIn_range'_aux (i := n) (m := m) n init inv hstep (by omega)
    simp_all only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]

theorem triple_forIn_range {β}
  (xs : Std.Legacy.Range) (init : β) (f : Nat → β → m (ForInStep β))
  (inv : Nat → β → l)
  (hstep : ∀ i b,
    triple
      (inv i b)
      (f i b)
      (fun | .yield b' => inv (i + xs.step) b' | .done b' => inv (xs.start + ((xs.stop - xs.start + xs.step - 1) / xs.step) * xs.step) b')) :
  triple (inv xs.start init) (forIn xs init f) (inv (xs.start + ((xs.stop - xs.start + xs.step - 1) / xs.step) * xs.step)) := by
  simp; apply triple_forIn_range'; apply hstep

theorem triple_forIn_range_step1 {β}
  {xs : Std.Legacy.Range} {init : β} {f : Nat → β → m (ForInStep β)}
  (inv : Nat → β → l)
  (hstep : ∀ i b,
    triple
      (inv i b)
      (f i b)
      (fun | .yield b' => inv (i + xs.step) b' | .done b' => inv xs.stop b')) :
  xs.step = 1 ->
  xs.start ≤ xs.stop ->
  triple (inv xs.start init) (forIn xs init f) (inv xs.stop) := by
  have := triple_forIn_range (m := m)  xs init f inv
  intro h eq;
  simp [h] at *
  rw [Nat.add_sub_of_le eq] at this;
  solve_by_elim

end Loops


section Lift

variable [inst: CompleteLattice l] [MAlgOrdered m l]

theorem wp_except_handler_eq ε (hd : ε -> Prop) [IsHandler hd] (c : ExceptT ε m α) post :
  wp c post = wp (m := m) c (fun | .ok x => post x | .error e => ⌜hd e⌝) := by
    apply MAlg.lift_ExceptT


open ExceptionAsSuccess in
theorem wp_part_eq ε (c : ExceptT ε m α) post :
  wp c post = wp (m := m) c (fun | .ok x => post x | .error _ => ⊤ₗ) := by
    simp [wp_except_handler_eq]

open ExceptionAsFailure in
theorem wp_tot_eq ε (c : ExceptT ε m α) post :
  wp c post = wp (m := m) c (fun | .ok x => post x | .error _ => ⊥ₗ) := by
    simp [wp_except_handler_eq]


theorem ExceptT.wp_lift_hd {hd : ε -> Prop} (c : m α) (post : α -> l) [IsHandler hd] :
  wp (liftM (n := ExceptT ε m) c) post = wp (m := m) c post := by
  simp [wp_except_handler_eq, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, mk]
  rw [map_eq_pure_bind, wp_bind]; simp [wp_pure]

theorem ExceptionAsSuccess.ExceptT.wp_lift (c : m α) (post : α -> l) :
  wp (liftM (n := ExceptT ε m) c) post = wp (m := m) c post := by
  apply ExceptT.wp_lift_hd

theorem ExceptionAsFailure.ExceptT.wp_lift (c : m α) (post : α -> l) :
  wp (liftM (n := ExceptT ε m) c) post = wp (m := m) c post := by
  apply ExceptT.wp_lift_hd

/- WP for DivM in TotalCorrectness -/
open TotalCorrectness in
theorem TotalCorrectness.DivM.wp_eq (α : Type) (x : DivM α) (post : α -> Prop) :
  wp x post =
    match x with
    | .div => False
    | .res r => post r := by
  simp +instances [wp, liftM, monadLift, MAlg.lift, Functor.map, TotalCorrectness.instMAlgOrderedDivMProp, Id]
  cases x <;> simp +instances [Loom.Order.embed]

/- WP for DivM in PartialCorrectness -/
theorem PartialCorrectness.DivM.wp_eq (α : Type) (x : DivM α) (post : α -> Prop) :
  wp x post =
    match x with
    | .div => True
    | .res r => post r := by
  simp +instances [wp, liftM, monadLift, MAlg.lift, Functor.map, PartialCorrectness.instMAlgOrderedDivMProp, Id]
  cases x <;> simp

/- WP for StateT in underlying monad -/
theorem StateT.wp_eq (c : StateT σ m α) (post : α -> σ -> l) :
  wp c post = fun s => wp (m := m) (c s) (fun xs => post xs.1 xs.2) := by
  simp [wp, liftM, monadLift, MAlg.lift_StateT];

/- WP for lift to StateT -/
theorem StateT.wp_lift (c : m α) (post : α -> σ -> l) :
  wp (liftM (n := StateT σ m) c) post = fun s => wp (m := m) c (post · s) := by
  simp [wp, liftM, monadLift, MAlg.lift_StateT, MonadLift.monadLift, StateT.lift];
  have liftE : ∀ α, MAlg.lift (m := m) (α := α) = wp := by intros; ext; simp +instances [wp, liftM, monadLift, ContT.run, Id]
  ext s; rw [map_eq_pure_bind, liftE, liftE, wp_bind]; simp [wp_pure]

/- WP for ReaderT in underlying monad  -/
theorem ReaderT.wp_eq (c : ReaderT σ m α) (post : α -> σ -> l) :
  wp c post = fun s => wp (m := m) (c s) (post · s) := by
  simp [wp, liftM, monadLift, MAlg.lift_ReaderT];

/- WP for lift to ReaderT -/
theorem ReaderT.wp_lift (c : m α) (post : α -> σ -> l) :
  wp (liftM (n := ReaderT σ m) c) post = fun s => wp (m := m) c (post · s) := by
  simp [wp, liftM, monadLift, MAlg.lift_ReaderT, MonadLift.monadLift]

/- WP lift from MAlgLift-/
omit [LawfulMonad m] in
theorem MAlgLift.wp_lift [Monad n] [CompleteLattice k] [MAlgOrdered n k] [MonadLiftT m n]
  -- [MonadLiftT (Cont l) (Cont k)]
  [mAlgLift : MAlgLiftT m l n k] (c : m α):
  wp (liftM (n := n) c) = fun (post : α -> k) => mAlgLift.cl.lift.monadLift (wp c) post := by
  ext;
  apply MAlgLiftT.μ_lift

end Lift

section ExceptT

variable [inst: CompleteLattice l] [MAlgOrdered m l] [IsHandler (ε := ε) hd]

/- WP for exception in ExceptT -/
theorem ExceptT.wp_throw (e : ε) :
  wp (α := α) (throw (m := ExceptT ε m) e) = fun _ => ⌜hd e⌝ := by
    ext; simp [wp_except_handler_eq, throw, throwThe, MonadExceptOf.throw, mk, wp_pure]

/- WP lift from Monad Transformer Algebra -/
theorem MAlgLift.wp_throw
  [Monad n] [CompleteLattice k] [MAlgOrdered n k] [MonadLiftT m n]
  [MonadLiftT (ExceptT ε m) n]
  [inst: MAlgLiftT (ExceptT ε m) l n k] :
    wp (α := α) (liftM (n := n) (throw (m := ExceptT ε m) e)) post = ⌜hd e⌝ := by
    rw [MAlgLift.wp_lift, ExceptT.wp_throw]
    simp only [Loom.Order.embed]; split
    · have tmp := inst.cl.lift_top (α := α) ; simp [Loom.Order.top] at tmp ; exact congrFun tmp _
    · have tmp := inst.cl.lift_bot (α := α) ; simp [Loom.Order.bot] at tmp ; exact congrFun tmp _

end ExceptT

section StateT

variable [inst: CompleteLattice l] [MAlgOrdered m l]

/- WP for get in StateT -/
theorem StateT.wp_get (post : σ -> σ -> l) :
  wp (get (m := StateT σ m)) post = fun s => post s s := by
  simp [StateT.wp_eq, get, getThe, MonadStateOf.get, StateT.get, wp_pure]

/- WP for set in StateT -/
theorem StateT.wp_set {res: σ} (post : PUnit -> σ -> l) :
  wp (set (m := StateT σ m) res) post = fun _ => post PUnit.unit res := by
  simp [StateT.wp_eq, set, StateT.set, wp_pure]

/- WP for modifyGet in StateT -/
theorem StateT.wp_modifyGet (post : α -> σ -> l) :
  wp (modifyGet (m := StateT σ m) f) post = fun s => post (f s).1 (f s).2 := by
  simp [StateT.wp_eq, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, wp_pure]

end StateT

section ReaderT

variable [inst: CompleteLattice l] [MAlgOrdered m l]

/- WP for read in ReaderT -/
theorem ReaderT.wp_read (post : σ -> σ -> l) :
  wp (read (m := ReaderT σ m)) post = fun s => post s s := by
  simp [ReaderT.wp_eq, read, readThe, MonadReaderOf.read, ReaderT.read, wp_pure]


end ReaderT
