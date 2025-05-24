import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import LoL.MonadAlgebras.WP.Basic
import LoL.MonadAlgebras.WP.Tactic
import LoL.MonadAlgebras.WP.Gen

universe u v w

section NonDetermenisticTransformer

inductive NonDetT (m : Type u -> Type v) : (α : Type u) -> Type _ where
  | pure {α} (ret : α) : NonDetT m α
  | vis {α} {β} (x : m β) (f : β → NonDetT m α) : NonDetT m α
  | pickCont {α} (τ : Type u) (p : τ -> Prop) (f : τ → NonDetT m α) : NonDetT m α
  | repeatCont {α} {β} (init : β) (f : β -> NonDetT m (ForInStep β)) (cont : β -> NonDetT m α) : NonDetT m α

variable {m : Type u -> Type v} {α β : Type u} [Monad m]

def NonDetT.bind (x : NonDetT m α) (f : α → NonDetT m β) : NonDetT m β :=
  match x with
  | pure ret => f ret
  | vis x f' => vis x fun y => bind (f' y) f
  | pickCont τ p f' => pickCont τ p fun t => bind (f' t) f
  | repeatCont init f' cont => repeatCont init f' fun t => bind (cont t) f

instance : Monad (NonDetT m) where
  pure := NonDetT.pure
  bind := NonDetT.bind

instance [LawfulMonad m] : LawfulMonad (NonDetT m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  { introv; induction x
    <;> simp [Functor.map, NonDetT.bind]
    <;> solve_by_elim [funext] }
  { introv; simp [bind, NonDetT.bind] }
  introv; induction x
  <;> simp [bind, NonDetT.bind]
  <;> solve_by_elim [funext]

variable [CompleteBooleanAlgebra l] [MPropOrdered m l]

lemma meet_himp (x x' y z : l) :
  x = x' ->
  (x ⇨ y) ⊓ (x' ⇨ z) = x ⇨ (y ⊓ z) := by
  rintro rfl
  simp [himp_eq]; rw [@sup_inf_right]

def NonDetT.pick (τ : Type u) : NonDetT m τ :=
  NonDetT.pickCont _ (fun _ => True) pure
def NonDetT.assume (as : Prop) : NonDetT m PUnit :=
  NonDetT.pickCont PUnit (fun _ => as) fun _ => pure .unit
def NonDetT.pickSuchThat (τ : Type u) (p : τ → Prop) : NonDetT m τ :=
  NonDetT.pickCont τ p pure
def NonDetT.repeat (init : α) (f : α -> NonDetT m (ForInStep α)) : NonDetT m α :=
  NonDetT.repeatCont init f pure

class MonadNonDet (m : Type u → Type v) where
  pick : (τ : Type u) →  m τ
  pickSuchThat : (τ : Type u) → (τ → Prop) → m τ
  assume : Prop → m PUnit.{u+1}
  rep {α : Type u} : α → (α → m (ForInStep α)) → m α

export MonadNonDet (pick assume pickSuchThat rep)


instance : MonadNonDet (NonDetT m) where
  pick   := .pick
  assume := .assume
  pickSuchThat := .pickSuchThat
  rep := .repeat

namespace DemonicChoice

noncomputable
def NonDetT.wp : {α : Type u} -> NonDetT m α -> Cont l α
  | _, .pure ret => pure ret
  | _, .vis x f => fun post => _root_.wp x fun a => wp (f a) post
  | _, .pickCont _ p f => fun post => ⨅ a, ⌜p a⌝ ⇨ wp (f a) post
  | _, @NonDetT.repeatCont _ _ β init f cont => fun post => ⨆ (inv : ForInStep β -> l),
      ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
      spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post)

omit [MPropOrdered m l] in
lemma spec_mono {α : Type u} (pre : l) (post : α -> l) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  spec pre post f <= spec pre post g := by
    unfold spec; intro
    refine inf_le_inf (by rfl) ?_
    refine LE.pure_imp (post ≤ f) (post ≤ g) ?_
    intro h a; apply le_trans; apply h a; solve_by_elim

lemma NonDetT.wp_mono [LawfulMonad m] {α : Type u} (x : NonDetT m α) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  NonDetT.wp x f <= NonDetT.wp x g := by
    intro h; induction x
    <;> simp [NonDetT.wp, pure, h, -le_himp_iff, -iSup_le_iff]
    <;> try solve_by_elim [wp_cons, iInf_le_of_le, himp_le_himp_left]
    apply iSup_mono; intro inv
    solve_by_elim [wp_cons, spec_mono, inf_le_inf_left]
lemma NonDetT.wp_bind [LawfulMonad m] {α β : Type u} (x : NonDetT m α) (f : α -> NonDetT m β)
  (post : β -> l):
  NonDetT.wp (x.bind f) post = NonDetT.wp x (fun x => NonDetT.wp (f x) post) := by
    unhygienic induction x
    <;> simp [NonDetT.wp, bind, pure, -le_himp_iff, -iSup_le_iff, NonDetT.bind]
    { simp [f_ih] }
    { simp [f_ih] }
    simp [cont_ih]

noncomputable
def NonDetT.μ : NonDetT m l -> l := fun x => NonDetT.wp x id

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

noncomputable
scoped
instance {l : outParam (Type u)} [CompleteBooleanAlgebra l] [MPropOrdered m l] [LawfulMonad m] : MPropOrdered (NonDetT m) l where
  μ := NonDetT.μ
  μ_ord_pure := by
    intro l; simp [NonDetT.μ, NonDetT.wp]; rfl
  μ_ord_bind := by
    simp [NonDetT.μ, bind, NonDetT.wp_bind]; intros
    solve_by_elim [NonDetT.wp_mono]

lemma NonDetT.wp_eq_wp {α : Type u} (x : NonDetT m α) (post : α -> l) :
  _root_.wp x post = NonDetT.wp x post := by
    simp [_root_.wp, liftM, monadLift, MProp.lift, MPropOrdered.μ, NonDetT.μ]
    erw [map_eq_pure_bind, NonDetT.wp_bind]
    rfl


@[simp]
lemma NonDetT.wp_vis {β : Type u} (x : m β) (f : β → NonDetT m α) post :
  _root_.wp (NonDetT.vis x f) post = _root_.wp x fun a => _root_.wp (f a) post := by
  simp [NonDetT.wp_eq_wp]; rfl

lemma NonDetT.wp_lift (c : m α) post :
  _root_.wp (liftM (n := NonDetT m) c) post = _root_.wp c post := by
  simp [NonDetT.wp_eq_wp]; rfl

@[simp]
lemma NonDetT.wp_pickCont {τ : Type u} p (f : τ → NonDetT m α) post :
  _root_.wp (NonDetT.pickCont τ p f) post = ⨅ a, ⌜p a⌝ ⇨ _root_.wp (f a) post := by
  simp [NonDetT.wp_eq_wp]; rfl

@[simp]
lemma NonDetT.wp_repeatCont {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) (cont : α -> NonDetT m β) post :
  _root_.wp (NonDetT.repeatCont init f cont) post = ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post) := by
  simp [NonDetT.wp_eq_wp]; rfl

@[simp]
lemma NonDetT.wp_pure (x : α) post :
  _root_.wp (NonDetT.pure (m := m) x) post = post x := by erw [_root_.wp_pure]

lemma MonadNonDet.wp_pick {τ : Type u} post :
  _root_.wp (MonadNonDet.pick (m := NonDetT m) τ) post = iInf post := by
  simp [MonadNonDet.pick, NonDetT.pick]

lemma MonadNonDet.wp_assume {as : Prop} post : _root_.wp (MonadNonDet.assume (m := NonDetT m) as) post = ⌜as⌝ ⇨ post .unit := by
  simp [MonadNonDet.assume, NonDetT.assume, iInf_const]

lemma MonadNonDet.wp_pickSuchThat {τ : Type u} (p : τ → Prop) post :
  _root_.wp (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) post = ⨅ a, ⌜p a⌝ ⇨ post a := by
  simp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]

lemma MonadNonDet.wp_repeat {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) post :
  _root_.wp (MonadNonDet.rep (m := NonDetT m) init f) post = ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) post := by
  simp [MonadNonDet.rep, NonDetT.repeat, NonDetT.wp, pure, NonDetT.wp_eq_wp]

instance [MonadNonDet m] : ForIn m Lean.Loop Unit where
  forIn {β} _ _ init f := @MonadNonDet.rep m _ β init (f ())

lemma MonadNonDet.wp_forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetT m (ForInStep β))
  (inv : β -> l) (on_done' : β -> l) :
  (∀ b, inv b <= wp (f () b) (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b')) ->
  triple (inv init) (forIn (m := NonDetT m) Lean.Loop.mk init f) (fun b => inv b ⊓ on_done' b) := by
  intro hstep; simp [triple]; erw [MonadNonDet.wp_repeat]
  refine le_iSup_of_le (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b') ?_
  simp [spec, hstep]


@[wpSimp, spec]
noncomputable
def WPGen.forWithInvariantLoop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {β}
  {init : β} {f : Unit -> β → NonDetT m (ForInStep β)}
  (inv : β → l) (on_done' : β → l) :
    WPGen (forIn Lean.Loop.mk init (fun u b => do
        invariantGadget (inv b)
        onDoneGadget (on_done' b)
        f u b)) := by
  apply WPGen.spec_triple_invs (invs :=
    (∀ b, triple (inv b) (f () b) (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b')))
  intro h; simp [invariantGadget, onDoneGadget]
  solve_by_elim [MonadNonDet.wp_forIn]

end DemonicChoice

namespace AngelicChoice

noncomputable
def   NonDetT.wp : {α : Type u} -> NonDetT m α -> Cont l α
  | _, .pure ret => pure ret
  | _, .vis x f => fun post => _root_.wp x fun a => wp (f a) post
  | _, .pickCont _ p f => fun post => ⨆ a, ⌜p a⌝ ⊓ wp (f a) post
  | _, .repeatCont init f cont => fun post => ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post)

omit [MPropOrdered m l] in
lemma spec_mono {α : Type u} (pre : l) (post : α -> l) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  spec pre post f <= spec pre post g := by
    unfold spec; intro
    refine inf_le_inf (by rfl) ?_
    refine LE.pure_imp (post ≤ f) (post ≤ g) ?_
    intro h a; apply le_trans; apply h a; solve_by_elim

lemma NonDetT.wp_mono [LawfulMonad m] {α : Type u} (x : NonDetT m α) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  NonDetT.wp x f <= NonDetT.wp x g := by
    intro h; induction x
    <;> simp [NonDetT.wp, pure, h, -le_himp_iff, -iSup_le_iff]
    <;> try solve_by_elim [wp_cons, le_iSup_of_le, inf_le_inf_left, iSup_mono]
    apply iSup_mono; intro inv
    solve_by_elim [wp_cons, spec_mono, inf_le_inf_left]
lemma NonDetT.wp_bind [LawfulMonad m] {α β : Type u} (x : NonDetT m α) (f : α -> NonDetT m β)
  (post : β -> l):
  NonDetT.wp (x.bind f) post = NonDetT.wp x (fun x => NonDetT.wp (f x) post) := by
    unhygienic induction x
    <;> simp [NonDetT.wp, bind, pure, -le_himp_iff, -iSup_le_iff, NonDetT.bind]
    { simp [f_ih] }
    { simp [f_ih] }
    simp [cont_ih]

noncomputable
def NonDetT.μ : NonDetT m l -> l := fun x => NonDetT.wp x id

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

noncomputable
scoped
instance {l : outParam (Type u)} [CompleteBooleanAlgebra l] [MPropOrdered m l] [LawfulMonad m] : MPropOrdered (NonDetT m) l where
  μ := NonDetT.μ
  μ_ord_pure := by
    intro l; simp [NonDetT.μ, NonDetT.wp]; rfl
  μ_ord_bind := by
    simp [NonDetT.μ, bind, NonDetT.wp_bind]; intros
    solve_by_elim [NonDetT.wp_mono]

lemma NonDetT.wp_eq_wp {α : Type u} (x : NonDetT m α) (post : α -> l) :
  _root_.wp x post = NonDetT.wp x post := by
    simp [_root_.wp, liftM, monadLift, MProp.lift, MPropOrdered.μ, NonDetT.μ]
    erw [map_eq_pure_bind, NonDetT.wp_bind]
    rfl


@[simp]
lemma NonDetT.wp_vis {β : Type u} (x : m β) (f : β → NonDetT m α) post :
  _root_.wp (NonDetT.vis x f) post = _root_.wp x fun a => _root_.wp (f a) post := by
  simp [NonDetT.wp_eq_wp]; rfl

lemma NonDetT.wp_lift (c : m α) post :
  _root_.wp (liftM (n := NonDetT m) c) post = _root_.wp c post := by
  simp [NonDetT.wp_eq_wp]; rfl

@[simp]
lemma NonDetT.wp_pickCont {τ : Type u} p (f : τ → NonDetT m α) post :
  _root_.wp (NonDetT.pickCont τ p f) post = ⨆ a, ⌜p a⌝ ⊓ _root_.wp (f a) post := by
  simp [NonDetT.wp_eq_wp]; rfl

@[simp]
lemma NonDetT.wp_repeatCont {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) (cont : α -> NonDetT m β) post :
  _root_.wp (NonDetT.repeatCont init f cont) post = ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post) := by
  simp [NonDetT.wp_eq_wp]; rfl

@[simp]
lemma NonDetT.wp_pure (x : α) post :
  _root_.wp (NonDetT.pure (m := m) x) post = post x := by erw [_root_.wp_pure]

lemma MonadNonDet.wp_pick {τ : Type u} post :
  _root_.wp (MonadNonDet.pick (m := NonDetT m) τ) post = iSup post := by
  simp [MonadNonDet.pick, NonDetT.pick]

lemma MonadNonDet.wp_assume {as : Prop} post : _root_.wp (MonadNonDet.assume (m := NonDetT m) as) post = ⌜as⌝ ⊓ post .unit := by
  simp [MonadNonDet.assume, NonDetT.assume, iSup_const]

lemma MonadNonDet.wp_pickSuchThat {τ : Type u} (p : τ → Prop) post :
  _root_.wp (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) post = ⨆ a, ⌜p a⌝ ⊓ post a := by
  simp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]

lemma MonadNonDet.wp_repeat {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) post :
  _root_.wp (MonadNonDet.rep (m := NonDetT m) init f) post = ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) post := by
  simp [MonadNonDet.rep, NonDetT.repeat, NonDetT.wp, pure, NonDetT.wp_eq_wp]

instance [MonadNonDet m] : ForIn m Lean.Loop Unit where
  forIn {β} _ _ init f := @MonadNonDet.rep m _ β init (f ())

lemma MonadNonDet.wp_forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetT m (ForInStep β))
  (inv : β -> l) (on_done' : β -> l) :
  (∀ b, inv b <= wp (f () b) (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b')) ->
  triple (inv init) (forIn (m := NonDetT m) Lean.Loop.mk init f) (fun b => inv b ⊓ on_done' b) := by
  intro hstep; simp [triple]; erw [MonadNonDet.wp_repeat]
  refine le_iSup_of_le (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b') ?_
  simp [spec, hstep]

@[wpSimp, spec]
noncomputable
def WPGen.forWithInvariantLoop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] {β}
  {init : β} {f : Unit -> β → NonDetT m (ForInStep β)}
  (inv : β → l) (on_done' : β → l) :
    WPGen (forIn Lean.Loop.mk init (fun u b => do
        invariantGadget (inv b)
        onDoneGadget (on_done' b)
        f u b)) := by
  apply WPGen.spec_triple_invs (invs :=
    (∀ b, triple (inv b) (f () b) (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b')))
  intro h; simp [invariantGadget, onDoneGadget]
  solve_by_elim [MonadNonDet.wp_forIn]

end AngelicChoice
