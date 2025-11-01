import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import Loom.MonadAlgebras.WP.Basic
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.Gen

universe u v w

section NonDeterministicTransformer

inductive NonDetT (m : Type u -> Type v) : (α : Type u) -> Type _ where
  | pure {α} (ret : α) : NonDetT m α
  | vis {α} {β} (x : m β) (f : β → NonDetT m α) : NonDetT m α
  | pickCont {α} (τ : Type u) (p : τ -> Prop) (f : τ → NonDetT m α) : NonDetT m α

variable {m : Type u -> Type v} {α β : Type u} [Monad m]

def NonDetT.bind (x : NonDetT m α) (f : α → NonDetT m β) : NonDetT m β :=
  match x with
  | pure ret => f ret
  | vis x f' => vis x fun y => bind (f' y) f
  | pickCont τ p f' => pickCont τ p fun t => bind (f' t) f

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

variable [CompleteBooleanAlgebra l] [MAlgOrdered m l]

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

class MonadNonDet (m : Type u → Type v) where
  pick : (τ : Type u) →  m τ
  pickSuchThat : (τ : Type u) → (τ → Prop) → m τ
  assume : Prop → m PUnit.{u+1}

export MonadNonDet (pick assume pickSuchThat)


instance : MonadNonDet (NonDetT m) where
  pick   := .pick
  assume := .assume
  pickSuchThat := .pickSuchThat

-- namespace PartialCorrectness
namespace DemonicChoice

def NonDetT.wp {l : Type u} {α : Type u} [CompleteLattice l] [MAlgOrdered m l] : NonDetT m α -> Cont l α
  | .pure ret => pure ret
  | .vis x f => fun post => _root_.wp x fun a => wp (f a) post
  | .pickCont τ p f => fun post => let p : Set τ := p; ⨅ a ∈ (p : Set τ), wp (f a) post

omit [MAlgOrdered m l] in
lemma spec_mono {α : Type u}  {l : Type u} [CompleteLattice l] (pre : l) (post : α -> l) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  spec pre post f <= spec pre post g := by
    unfold spec; intro
    refine inf_le_inf (by rfl) ?_
    refine LE.pure_imp (post ≤ f) (post ≤ g) ?_
    intro h a; apply le_trans; apply h a; solve_by_elim

lemma NonDetT.wp_mono  {l : Type u} [CompleteLattice l] [MAlgOrdered m l] [LawfulMonad m] {α : Type u} (x : NonDetT m α) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  NonDetT.wp x f <= NonDetT.wp x g := by
    intro h; induction x
    <;> simp [NonDetT.wp, pure, h, -le_himp_iff, -iSup_le_iff]
    <;> try solve_by_elim [wp_cons, iInf_le_of_le, himp_le_himp_left]
    intro _ _; solve_by_elim [iInf₂_le_of_le]
lemma NonDetT.wp_bind  {l : Type u} [CompleteLattice l] [MAlgOrdered m l] [LawfulMonad m] {α β : Type u} (x : NonDetT m α) (f : α -> NonDetT m β)
  (post : β -> l):
  NonDetT.wp (x.bind f) post = NonDetT.wp x (fun x => NonDetT.wp (f x) post) := by
    unhygienic induction x
    <;> simp [NonDetT.wp, pure, -le_himp_iff, -iSup_le_iff, NonDetT.bind]
    { simp [f_ih] }
    simp [f_ih]

noncomputable
def NonDetT.μ  {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : NonDetT m l -> l := fun x => NonDetT.wp x id

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

noncomputable
scoped
instance {l : Type u} [CompleteLattice l] [MAlgOrdered m l] [LawfulMonad m] : MAlgOrdered (NonDetT m) l where
  μ := NonDetT.μ
  μ_ord_pure := by
    intro l; simp [NonDetT.μ, NonDetT.wp]; rfl
  μ_ord_bind := by
    simp [NonDetT.μ, bind, NonDetT.wp_bind]; intros
    solve_by_elim [NonDetT.wp_mono]

lemma NonDetT.wp_eq_wp {α : Type u} (x : NonDetT m α) (post : α -> l) :
  _root_.wp x post = NonDetT.wp x post := by
    simp [_root_.wp, liftM, monadLift, MAlg.lift, MAlgOrdered.μ, NonDetT.μ]
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
  simp [NonDetT.wp_eq_wp, NonDetT.wp]; congr; ext x
  simp [Membership.mem, Set.Mem]
  by_cases h: p x <;> simp [h]


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

lemma NonDetT.wp_iInf {ι : Type u} {α : Type u} {l : Type u} [CompleteBooleanAlgebra l] [MAlgOrdered m l] [MAlgDet m l] [Nonempty ι]
  (x : NonDetT m α) (post : ι -> α -> l) :
  _root_.wp x (fun a => iInf post a) = ⨅ i, _root_.wp x (post i) := by
  simp [NonDetT.wp_eq_wp]
  unhygienic induction x <;> simp [NonDetT.wp, pure, *]
  { erw [_root_.wp_iInf] }
  rw [iInf_psigma', iInf_comm]; congr!; simp [iInf_psigma']

instance [NoFailure m] : NoFailure (NonDetT m) where
  noFailure := by
    intro α c
    have : MAlg.lift c = wp c := by rfl
    rw [this, NonDetT.wp_eq_wp]; clear this
    induction c <;> simp [NonDetT.wp, pure, *]

noncomputable
scoped
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l]
  [inst: MAlgOrdered m l] :
  MAlgLift m l (NonDetT m) l where
    cl := by exact LogicLift.refl
    μ_lift := by
      intros; simp [liftM, monadLift, MonadLift.monadLift, MAlgOrdered.μ, NonDetT.μ, NonDetT.wp,
        pure, wp, MAlg.lift, Functor.map, NonDetT.wp, NonDetT.bind,LogicLift.refl]

end DemonicChoice

namespace AngelicChoice

noncomputable
def   NonDetT.wp {l : Type u} {α : Type u} [CompleteLattice l] [MAlgOrdered m l] : NonDetT m α -> Cont l α
  | .pure ret => pure ret
  | .vis x f => fun post => _root_.wp x fun a => wp (f a) post
  | .pickCont _ p f => fun post => ⨆ a, ⌜p a⌝ ⊓ wp (f a) post

lemma spec_mono {α : Type u} {l : Type u} [CompleteLattice l] (pre : l) (post : α -> l) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  spec pre post f <= spec pre post g := by
    unfold spec; intro
    refine inf_le_inf (by rfl) ?_
    refine LE.pure_imp (post ≤ f) (post ≤ g) ?_
    intro h a; apply le_trans; apply h a; solve_by_elim

lemma NonDetT.wp_mono [LawfulMonad m] {α : Type u} {l : Type u} [CompleteLattice l] [MAlgOrdered m l] (x : NonDetT m α) (f g : α -> l) :
  (∀ a, f a <= g a) ->
  NonDetT.wp x f <= NonDetT.wp x g := by
    intro h; induction x
    <;> simp [NonDetT.wp, pure, h, -le_himp_iff, -iSup_le_iff]
    <;> try solve_by_elim [wp_cons, le_iSup_of_le, inf_le_inf_left, iSup_mono]

lemma NonDetT.wp_bind [LawfulMonad m] {α β : Type u} {l : Type u} [CompleteLattice l] [MAlgOrdered m l] (x : NonDetT m α) (f : α -> NonDetT m β)
  (post : β -> l):
  NonDetT.wp (x.bind f) post = NonDetT.wp x (fun x => NonDetT.wp (f x) post) := by
    unhygienic induction x
    <;> simp [NonDetT.wp, pure, -le_himp_iff, -iSup_le_iff, NonDetT.bind]
    { simp [f_ih] }
    simp [f_ih]

noncomputable
def NonDetT.μ {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : NonDetT m l -> l := fun x => NonDetT.wp x id

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

noncomputable
scoped
instance {l : outParam (Type u)} [CompleteLattice l] [MAlgOrdered m l] [LawfulMonad m] : MAlgOrdered (NonDetT m) l where
  μ := NonDetT.μ
  μ_ord_pure := by
    intro l; simp [NonDetT.μ, NonDetT.wp]; rfl
  μ_ord_bind := by
    simp [NonDetT.μ, bind, NonDetT.wp_bind]; intros
    solve_by_elim [NonDetT.wp_mono]

lemma NonDetT.wp_eq_wp {α : Type u} (x : NonDetT m α) (post : α -> l) :
  _root_.wp x post = NonDetT.wp x post := by
    simp [_root_.wp, liftM, monadLift, MAlg.lift, MAlgOrdered.μ, NonDetT.μ]
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

noncomputable
scoped
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l]
  [inst: MAlgOrdered m l] :
  MAlgLift m l (NonDetT m) l where
    cl := by exact LogicLift.refl
    μ_lift := by
      intros; simp [liftM, monadLift, MonadLift.monadLift, MAlgOrdered.μ, NonDetT.μ, NonDetT.wp,
        pure, wp, MAlg.lift, Functor.map, NonDetT.wp, NonDetT.bind, LogicLift.refl]

end AngelicChoice
