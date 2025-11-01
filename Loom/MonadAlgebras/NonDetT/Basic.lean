import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import Loom.MonadAlgebras.WP.Basic
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.Gen

import Loom.MonadAlgebras.NonDetT.Findable

universe u v w

section NonDeterministicTransformer

/- NonDetT transformer definition -/
inductive NonDetT (m : Type u -> Type v) : (α : Type u) -> Type _ where
  | pure {α} (ret : α) : NonDetT m α
  | vis {α} {β} (x : m β) (f : β → NonDetT m α) : NonDetT m α
  | pickCont {α} (τ : Type u) (p : τ -> Prop) [Findable p] (f : τ → NonDetT m α) : NonDetT m α
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

variable [CompleteBooleanAlgebra l] [MAlgOrdered m l]

lemma meet_himp (x x' y z : l) :
  x = x' ->
  (x ⇨ y) ⊓ (x' ⇨ z) = x ⇨ (y ⊓ z) := by
  rintro rfl
  simp [himp_eq]; rw [@sup_inf_right]

def NonDetT.pick (τ : Type u) [Inhabited τ] : NonDetT m τ :=
  NonDetT.pickCont _ (fun _ => True) pure
def NonDetT.assume (as : Prop) [Decidable as] : NonDetT m PUnit :=
  NonDetT.pickCont PUnit (fun _ => as) fun _ => pure .unit
def NonDetT.pickSuchThat (τ : Type u) (p : τ → Prop) [Findable p] : NonDetT m τ :=
  NonDetT.pickCont τ p pure
def NonDetT.repeat (init : α) (f : α -> NonDetT m (ForInStep α)) : NonDetT m α :=
  NonDetT.repeatCont init f pure

/- Non Determinism Monad typeclass -/
class MonadNonDet (m : Type u → Type v) where
  pick : (τ : Type u) → [Inhabited τ] → m τ
  -- get a value with given property
  pickSuchThat : (τ : Type u) → (p : τ → Prop) → [Findable p] → m τ
  assume : (as : Prop) → [Decidable as] → m PUnit.{u+1}
  -- loop instance
  rep {α : Type u} : α → (α → m (ForInStep α)) → m α

export MonadNonDet (pick assume pickSuchThat rep)


instance : MonadNonDet (NonDetT m) where
  pick   := .pick
  assume := .assume
  pickSuchThat := .pickSuchThat
  rep := .repeat

namespace PartialCorrectness
namespace DemonicChoice

/- WP for NonDetT -/
noncomputable
def NonDetT.wp {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : {α : Type u} -> NonDetT m α -> Cont l α
  | _, .pure ret => pure ret
  | _, .vis x f => fun post => _root_.wp x fun a => wp (f a) post
  | _, @NonDetT.pickCont _ _ τ p _ f =>
  fun post =>
    let p : Set τ := p;
    ⨅ a ∈ (p : Set τ), wp (f a) post
  | _, @NonDetT.repeatCont _ _ β init f cont => fun post => ⨆ (inv : ForInStep β -> l),
      ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
      spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post)

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
    { intro _ _; solve_by_elim [iInf₂_le_of_le] }
    apply iSup_mono; intro inv
    solve_by_elim [wp_cons, spec_mono, inf_le_inf_left]
lemma NonDetT.wp_bind  {l : Type u} [CompleteLattice l] [MAlgOrdered m l] [LawfulMonad m] {α β : Type u} (x : NonDetT m α) (f : α -> NonDetT m β)
  (post : β -> l):
  NonDetT.wp (x.bind f) post = NonDetT.wp x (fun x => NonDetT.wp (f x) post) := by
    unhygienic induction x
    <;> simp [NonDetT.wp, pure, -le_himp_iff, -iSup_le_iff, NonDetT.bind]
    { simp [f_ih] }
    { simp [f_ih] }
    simp [cont_ih]

/- μ for NonDetT from NonDetT.wp -/
noncomputable
def NonDetT.μ  {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : NonDetT m l -> l := fun x => NonDetT.wp x id

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

/- Ordered Monad Algebra instance for NonDetT -/
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
lemma NonDetT.wp_pickCont {τ : Type u} p (f : τ → NonDetT m α) [Findable p] post :
  _root_.wp (NonDetT.pickCont τ p f) post =  ⨅ a, ⌜p a⌝ ⇨ _root_.wp (f a) post := by
  simp [NonDetT.wp_eq_wp, NonDetT.wp]; congr; ext x
  simp [Membership.mem, Set.Mem]
  by_cases h: p x <;> simp [h]

@[simp]
lemma NonDetT.wp_repeatCont {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) (cont : α -> NonDetT m β) post :
  _root_.wp (NonDetT.repeatCont init f cont) post = ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post) := by
  simp [NonDetT.wp_eq_wp]; rfl

@[simp]
lemma NonDetT.wp_pure (x : α) post :
  _root_.wp (NonDetT.pure (m := m) x) post = post x := by erw [_root_.wp_pure]

lemma MonadNonDet.wp_pick {τ : Type u} [Inhabited τ] post :
  _root_.wp (MonadNonDet.pick (m := NonDetT m) τ) post = iInf post := by
  simp [MonadNonDet.pick, NonDetT.pick]

lemma MonadNonDet.wp_assume {as : Prop} [Decidable as] post :
  _root_.wp (MonadNonDet.assume (m := NonDetT m) as) post = ⌜as⌝ ⇨ post .unit := by
  simp [MonadNonDet.assume, NonDetT.assume, iInf_const]

lemma MonadNonDet.wp_pickSuchThat {τ : Type u} (p : τ → Prop) [Findable p] post :
  _root_.wp (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) post = ⨅ a, ⌜p a⌝ ⇨ post a := by
  simp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]

lemma MonadNonDet.wp_repeat {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) post :
  _root_.wp (MonadNonDet.rep (m := NonDetT m) init f) post = ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) post := by
  simp [MonadNonDet.rep, NonDetT.repeat, NonDetT.wp, pure, NonDetT.wp_eq_wp]

instance [MonadNonDet m] : ForIn m Lean.Loop Unit where
  forIn {β} _ _ init f := @MonadNonDet.rep m _ β init (f ())

/- iteration lemma -/
lemma MonadNonDet.wp_forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetT m (ForInStep β))
  (inv : β -> l) (on_done' : β -> l) :
  (∀ b, inv b <= wp (f () b) (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b')) ->
  triple (inv init) (forIn (m := NonDetT m) Lean.Loop.mk init f) (fun b => inv b ⊓ on_done' b) := by
  intro hstep; simp [triple]; erw [MonadNonDet.wp_repeat]
  refine le_iSup_of_le (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b') ?_
  simp [spec, hstep]

/- VC generation for iteration -/
@[loomWpSimp, loomSpec]
noncomputable
def WPGen.forWithInvariantLoop {β}
  {init : β} {f : Unit -> β → NonDetT m (ForInStep β)}
  (inv : β → List l) (on_done' : β → l)
  (wpg : ∀ b, WPGen (f () b)) :
    WPGen (forIn Lean.Loop.mk init (fun u b => do
        invariantGadget (inv b)
        onDoneGadget (on_done' b)
        f u b)) where
    get := ⌜∀ b, invariants (inv b) <= (wpg b).get fun
      | .yield b' => invariants <| inv b'
      | .done b'  => invariants (inv b') ⊓ on_done' b'⌝
      ⊓ spec
      ((inv init).foldr (·⊓·) ⊤)
      (fun b => (inv b).foldr (·⊓·) ⊤ ⊓ on_done' b)
    prop := by
      intro post; simp only [LE.pure]; split_ifs with h <;> try simp
      apply (triple_spec ..).mpr
      simp [invariantGadget, onDoneGadget]
      apply MonadNonDet.wp_forIn (inv := fun b => (inv b).foldr (· ⊓ ·) ⊤)
      intro b; apply (wpg b).intro
      all_goals solve_by_elim
  -- apply WPGen.spec_triple_invs (invs :=
  --   (∀ b, triple (invariants (inv b)) (f () b) (fun | .yield b' => invariants (inv b') | .done b' => invariants (inv b') ⊓ on_done' b')))
  -- intro h; simp [invariantGadget, onDoneGadget]
  -- solve_by_elim [MonadNonDet.wp_forIn]

/- Monad Transformer Algebra for NonDetT -/
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

/- WP for NonDetT -/
noncomputable
def NonDetT.wp {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : {α : Type u} -> NonDetT m α -> Cont l α
  | _, .pure ret => pure ret
  | _, .vis x f => fun post => _root_.wp x fun a => wp (f a) post
  | _, @NonDetT.pickCont _ _ τ p _ f => fun post => ⨆ a, ⌜p a⌝ ⊓ wp (f a) post
  | _, .repeatCont init f cont => fun post => ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post)

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
    apply iSup_mono; intro inv
    solve_by_elim [wp_cons, spec_mono, inf_le_inf_left]
lemma NonDetT.wp_bind [LawfulMonad m] {α β : Type u} {l : Type u} [CompleteLattice l] [MAlgOrdered m l] (x : NonDetT m α) (f : α -> NonDetT m β)
  (post : β -> l):
  NonDetT.wp (x.bind f) post = NonDetT.wp x (fun x => NonDetT.wp (f x) post) := by
    unhygienic induction x
    <;> simp [NonDetT.wp, pure, -le_himp_iff, -iSup_le_iff, NonDetT.bind]
    { simp [f_ih] }
    { simp [f_ih] }
    simp [cont_ih]

/- μ for NonDetT from NonDetT.wp -/
noncomputable
def NonDetT.μ {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : NonDetT m l -> l := fun x => NonDetT.wp x id

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

/- Ordered Monad Algebra instance for NonDetT -/
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
lemma NonDetT.wp_pickCont {τ : Type u} p (f : τ → NonDetT m α) [Findable p] post :
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

lemma MonadNonDet.wp_pick {τ : Type u} [Inhabited τ] post :
  _root_.wp (MonadNonDet.pick (m := NonDetT m) τ) post = iSup post := by
  simp [MonadNonDet.pick, NonDetT.pick]

lemma MonadNonDet.wp_assume {as : Prop} [Decidable as] post : _root_.wp (MonadNonDet.assume (m := NonDetT m) as) post = ⌜as⌝ ⊓ post .unit := by
  simp [MonadNonDet.assume, NonDetT.assume, iSup_const]

lemma MonadNonDet.wp_pickSuchThat {τ : Type u} (p : τ → Prop) [Findable p] post :
  _root_.wp (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) post = ⨆ a, ⌜p a⌝ ⊓ post a := by
  simp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]

lemma MonadNonDet.wp_repeat {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) post :
  _root_.wp (MonadNonDet.rep (m := NonDetT m) init f) post = ⨆ (inv : ForInStep _ -> l),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) inv⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) post := by
  simp [MonadNonDet.rep, NonDetT.repeat, NonDetT.wp, pure, NonDetT.wp_eq_wp]

instance [MonadNonDet m] : ForIn m Lean.Loop Unit where
  forIn {β} _ _ init f := @MonadNonDet.rep m _ β init (f ())

/- iteration lemma -/
lemma MonadNonDet.wp_forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetT m (ForInStep β))
  (inv : β -> l) (on_done' : β -> l) :
  (∀ b, inv b <= wp (f () b) (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b')) ->
  triple (inv init) (forIn (m := NonDetT m) Lean.Loop.mk init f) (fun b => inv b ⊓ on_done' b) := by
  intro hstep; simp [triple]; erw [MonadNonDet.wp_repeat]
  refine le_iSup_of_le (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b') ?_
  simp [spec, hstep]

/- VC generation for iteration -/
@[loomWpSimp, loomSpec]
noncomputable
def WPGen.forWithInvariantLoop {β}
  {init : β} {f : Unit -> β → NonDetT m (ForInStep β)}
  (inv : β → List l) (on_done' : β → l)
  (wpg : ∀ b, WPGen (f () b)) :
    WPGen (forIn Lean.Loop.mk init (fun u b => do
        invariantGadget (inv b)
        onDoneGadget (on_done' b)
        f u b)) where
    get := ⌜∀ b, invariants (inv b) <= (wpg b).get fun
      | .yield b' => invariants <| inv b'
      | .done b'  => invariants (inv b') ⊓ on_done' b'⌝
      ⊓ spec
      ((inv init).foldr (·⊓·) ⊤)
      (fun b => (inv b).foldr (·⊓·) ⊤ ⊓ on_done' b)
    prop := by
      intro post; simp only [LE.pure]; split_ifs with h <;> try simp
      apply (triple_spec ..).mpr
      simp [invariantGadget, onDoneGadget]
      apply MonadNonDet.wp_forIn (inv := fun b => (inv b).foldr (· ⊓ ·) ⊤)
      intro b; apply (wpg b).intro
      all_goals solve_by_elim

/- Monad Transformer Algebra for NonDetT -/
noncomputable
scoped
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l]
  [inst: MAlgOrdered m l] :
  MAlgLift m l (NonDetT m) l where
    cl := by exact LogicLift.refl
    μ_lift := by
      intros; simp [liftM, monadLift, MonadLift.monadLift, MAlgOrdered.μ, NonDetT.μ, NonDetT.wp,
        pure, wp, MAlg.lift, Functor.map, NonDetT.wp, NonDetT.bind,LogicLift.refl]

end AngelicChoice

end PartialCorrectness

/- TODO: avoid code duplication -/
namespace TotalCorrectness

namespace DemonicChoice

/- WP for NonDetT -/
noncomputable
def NonDetT.wp {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : {α : Type u} -> NonDetT m α -> Cont l α
  | _, .pure ret => pure ret
  | _, .vis x f => fun post => _root_.wp x fun a => wp (f a) post
  | _, @NonDetT.pickCont _ _ τ p _ f => fun post => let p : Set τ := p; ⌜∃ h, p h⌝ ⊓  ⨅ a ∈ (p : Set τ), wp (f a) post
  | _, @NonDetT.repeatCont _ _ β init f cont => fun post => ⨆ (inv : ForInStep β -> l) (measure : β -> Nat),
      ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) (fun | .yield b' => inv (.yield b') ⊓ ⌜ measure b' < measure b ⌝ | .done b' => inv (.done b'))⌝ ⊓
      spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post)

omit [MAlgOrdered m l] in
lemma spec_mono {α : Type u}  {l : Type u} [CompleteLattice l] (pre : l) (post : α -> l) (f g : α -> l) :
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
    <;> try solve_by_elim [wp_cons, iInf_le_of_le, himp_le_himp_left]
    { intro _ _ _; solve_by_elim [iInf₂_le_of_le] }
    apply iSup_mono; intro inv; apply iSup_mono; intro wf
    solve_by_elim [wp_cons, spec_mono, inf_le_inf_left]

lemma NonDetT.wp_bind [LawfulMonad m] {α β : Type u} {l : Type u} [CompleteLattice l] [MAlgOrdered m l] (x : NonDetT m α) (f : α -> NonDetT m β)
  (post : β -> l):
  NonDetT.wp (x.bind f) post = NonDetT.wp x (fun x => NonDetT.wp (f x) post) := by
    unhygienic induction x
    <;> simp [NonDetT.wp, pure, -le_himp_iff, -iSup_le_iff, NonDetT.bind]
    { simp [f_ih] }
    { simp [f_ih] }
    simp [cont_ih]

/- μ for NonDetT from NonDetT.wp -/
noncomputable
def NonDetT.μ {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : NonDetT m l -> l := fun x => NonDetT.wp x id

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

/- Ordered Monad Algebra instance for NonDetT -/
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
lemma NonDetT.wp_pickCont {τ : Type u} p (f : τ → NonDetT m α) [Findable p] post :
  _root_.wp (NonDetT.pickCont τ p f) post = ⌜∃ h, p h⌝ ⊓ ⨅ a, ⌜p a⌝ ⇨ _root_.wp (f a) post := by
  simp [NonDetT.wp_eq_wp, NonDetT.wp]; congr; ext x
  simp [Membership.mem, Set.Mem]
  by_cases h: p x <;> simp [h]

@[simp]
lemma NonDetT.wp_repeatCont {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) (cont : α -> NonDetT m β) post :
  _root_.wp (NonDetT.repeatCont init f cont) post = ⨆ (inv : ForInStep _ -> l) (measure : _ → Nat),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) (fun | .yield b' => inv (.yield b') ⊓ ⌜ measure b' < measure b ⌝ | .done b' => inv (.done b'))⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post) := by
  simp [NonDetT.wp_eq_wp];
  rfl

@[simp]
lemma NonDetT.wp_pure (x : α) post :
  _root_.wp (NonDetT.pure (m := m) x) post = post x := by erw [_root_.wp_pure]

lemma MonadNonDet.wp_pick {τ : Type u} [Inhabited τ] post :
  _root_.wp (MonadNonDet.pick (m := NonDetT m) τ) post = iInf post := by
  simp [MonadNonDet.pick, NonDetT.pick]

lemma MonadNonDet.wp_assume {as : Prop} [Decidable as] post : _root_.wp (MonadNonDet.assume (m := NonDetT m) as) post = ⌜as⌝ ⊓ post .unit := by
  simp [MonadNonDet.assume, NonDetT.assume, iInf_const]

lemma MonadNonDet.wp_pickSuchThat {τ : Type u} (p : τ → Prop) [Findable p] post :
  _root_.wp (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) post = ⌜∃ h, p h⌝ ⊓ ⨅ a, ⌜p a⌝ ⇨ post a := by
  simp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]

lemma MonadNonDet.wp_repeat {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) post :
  _root_.wp (MonadNonDet.rep (m := NonDetT m) init f) post = ⨆ (inv : ForInStep _ -> l) (measure : _ → Nat),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) (fun | .yield b' => inv (.yield b') ⊓ ⌜ measure b' < measure b ⌝ | .done b' => inv (.done b'))⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) post := by
  simp [MonadNonDet.rep, NonDetT.repeat, NonDetT.wp, pure, NonDetT.wp_eq_wp]

instance [MonadNonDet m] : ForIn m Lean.Loop Unit where
  forIn {β} _ _ init f := @MonadNonDet.rep m _ β init (f ())

/- iteration lemma -/
lemma MonadNonDet.wp_forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetT m (ForInStep β))
  (inv : β -> l) (on_done' : β -> l) (measure: β → Nat):
  (∀ b, inv b <= wp (f () b) (fun | .yield b' => inv b' ⊓ ⌜ measure b' < measure b ⌝ | .done b' => inv b' ⊓ on_done' b')) ->
  triple (inv init) (forIn (m := NonDetT m) Lean.Loop.mk init f) (fun b => inv b ⊓ on_done' b) := by
  intro hstep; simp [triple]; erw [MonadNonDet.wp_repeat]
  refine le_iSup_of_le (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b') ?_
  simp; refine le_iSup_of_le ?_ ?_; assumption
  simp [spec, hstep]


/- VC generation for iteration -/
@[loomWpSimp, loomSpec]
noncomputable
def WPGen.forWithInvariantLoop {β}
  {init : β} {f : Unit -> β → NonDetT m (ForInStep β)}
  (inv : β → List l) (on_done' : β → l) (measure : β → Nat)
  (wpg : ∀ b, WPGen (f () b)) : WPGen (forIn Lean.Loop.mk init (fun u b => do
        invariantGadget (inv b)
        onDoneGadget (on_done' b)
        decreasingGadget (measure b)
        f u b)) where
    get := ⌜∀ b, invariants (inv b) <= (wpg b).get fun
      | .yield b' => (invariants (inv b')) ⊓ ⌜with_name_prefix `decreasing (measure b' < measure b)⌝
      | .done b'  => invariants (inv b') ⊓ on_done' b'⌝
      ⊓ spec
        ((inv init).foldr (·⊓·) ⊤)
        (fun b => (inv b).foldr (·⊓·) ⊤ ⊓ on_done' b)
    prop := by
      intro post; simp only [LE.pure]; split_ifs with h <;> try simp
      apply (triple_spec ..).mpr
      simp [invariantGadget, onDoneGadget, decreasingGadget]
      apply MonadNonDet.wp_forIn (inv := fun b => (inv b).foldr (· ⊓ ·) ⊤)
      intro b; apply (wpg b).intro
      solve_by_elim

/- Monad Transformer Algebra for NonDetT -/
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

/- WP for NonDetT -/
noncomputable
def   NonDetT.wp {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : {α : Type u} -> NonDetT m α -> Cont l α
  | _, .pure ret => pure ret
  | _, .vis x f => fun post => _root_.wp x fun a => wp (f a) post
  | _, @NonDetT.pickCont _ _ _ p _ f => fun post => ⨆ a, ⌜p a⌝ ⊓ wp (f a) post
  | _, .repeatCont init f cont => fun post => ⨆ (inv : ForInStep _ -> l) (measure : _ -> Nat),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) (fun | .yield b' => inv (.yield b') ⊓ ⌜ measure b' < measure b ⌝ | .done b' => inv (.done b'))⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post)

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
    apply iSup_mono; intro inv; apply iSup_mono; intro wf
    solve_by_elim [wp_cons, spec_mono, inf_le_inf_left]
lemma NonDetT.wp_bind [LawfulMonad m] {α β : Type u} {l : Type u} [CompleteLattice l] [MAlgOrdered m l] (x : NonDetT m α) (f : α -> NonDetT m β)
  (post : β -> l):
  NonDetT.wp (x.bind f) post = NonDetT.wp x (fun x => NonDetT.wp (f x) post) := by
    unhygienic induction x
    <;> simp [NonDetT.wp, pure, -le_himp_iff, -iSup_le_iff, NonDetT.bind]
    { simp [f_ih] }
    { simp [f_ih] }
    simp [cont_ih]

/- μ for NonDetT from NonDetT.wp -/
noncomputable
def NonDetT.μ {l : Type u} [CompleteLattice l] [MAlgOrdered m l] : NonDetT m l -> l := fun x => NonDetT.wp x id

instance : MonadLift m (NonDetT m) where
  monadLift x := NonDetT.vis x pure

variable [LawfulMonad m]

/- Ordered Monad Algebra instance for NonDetT -/
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
lemma NonDetT.wp_pickCont {τ : Type u} p (f : τ → NonDetT m α) [Findable p] post :
  _root_.wp (NonDetT.pickCont τ p f) post = ⨆ a, ⌜p a⌝ ⊓ _root_.wp (f a) post := by
  simp [NonDetT.wp_eq_wp]; rfl

@[simp]
lemma NonDetT.wp_repeatCont {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) (cont : α -> NonDetT m β) post :
  _root_.wp (NonDetT.repeatCont init f cont) post = ⨆ (inv : ForInStep _ -> l) (measure : _ -> Nat),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) (fun | .yield b' => inv (.yield b') ⊓ ⌜ measure b' < measure b ⌝ | .done b' => inv (.done b'))⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) (fun b => wp (cont b) post) := by
  simp [NonDetT.wp_eq_wp]; rfl

@[simp]
lemma NonDetT.wp_pure (x : α) post :
  _root_.wp (NonDetT.pure (m := m) x) post = post x := by erw [_root_.wp_pure]

lemma MonadNonDet.wp_pick {τ : Type u} [Inhabited τ] post :
  _root_.wp (MonadNonDet.pick (m := NonDetT m) τ) post = iSup post := by
  simp [MonadNonDet.pick, NonDetT.pick]

lemma MonadNonDet.wp_assume {as : Prop} [Decidable as] post : _root_.wp (MonadNonDet.assume (m := NonDetT m) as) post = ⌜as⌝ ⊓ post .unit := by
  simp [MonadNonDet.assume, NonDetT.assume, iSup_const]

lemma MonadNonDet.wp_pickSuchThat {τ : Type u} (p : τ → Prop) [Findable p] post :
  _root_.wp (MonadNonDet.pickSuchThat (m := NonDetT m) τ p) post = ⨆ a, ⌜p a⌝ ⊓ post a := by
  simp [MonadNonDet.pickSuchThat, NonDetT.pickSuchThat]

lemma MonadNonDet.wp_repeat {α : Type u} (init : α) (f : α -> NonDetT m (ForInStep α)) post :
  _root_.wp (MonadNonDet.rep (m := NonDetT m) init f) post = ⨆ (inv : ForInStep _ -> l) (measure : _ -> Nat),
    ⌜ ∀ b, (inv (ForInStep.yield b)) <= wp (f b) (fun | .yield b' => inv (.yield b') ⊓ ⌜ measure b' < measure b ⌝ | .done b' => inv (.done b'))⌝ ⊓
    spec (inv (.yield init)) (fun b => inv (.done b)) post := by
  simp [MonadNonDet.rep, NonDetT.repeat, NonDetT.wp, pure, NonDetT.wp_eq_wp]

instance [MonadNonDet m] : ForIn m Lean.Loop Unit where
  forIn {β} _ _ init f := @MonadNonDet.rep m _ β init (f ())

/- iteration lemma -/
lemma MonadNonDet.wp_forIn {β : Type u} (init : β) (f : Unit -> β -> NonDetT m (ForInStep β))
  (inv : β -> l) (on_done' : β -> l) (measure : β -> Nat) :
  (∀ b, inv b <= wp (f () b) (fun | .yield b' => inv b' ⊓ ⌜ measure b' < measure b ⌝ | .done b' => inv b' ⊓ on_done' b')) ->
  triple (inv init) (forIn (m := NonDetT m) Lean.Loop.mk init f) (fun b => inv b ⊓ on_done' b) := by
  intro hstep; simp [triple]; erw [MonadNonDet.wp_repeat]
  refine le_iSup_of_le (fun | .yield b' => inv b' | .done b' => inv b' ⊓ on_done' b') ?_
  simp; refine le_iSup_of_le ?_ ?_; assumption
  simp [spec, hstep]

/- VC generation for iteration -/
@[loomWpSimp, loomSpec]
noncomputable
def WPGen.forWithInvariantLoop {β}
  {init : β} {f : Unit -> β → NonDetT m (ForInStep β)}
  (inv : β → List l) (on_done' : β → l) (measure: β -> Nat) (wpg : ∀ b, WPGen (f () b)): WPGen (forIn Lean.Loop.mk init (fun u b => do
        invariantGadget (inv b)
        onDoneGadget (on_done' b)
        decreasingGadget (measure b)
        f u b)) where
    get := ⌜∀ b, invariants (inv b) <= (wpg b).get fun
      | .yield b' => (invariants (inv b')) ⊓ ⌜with_name_prefix `decreasing (measure b' < measure b)⌝
      | .done b'  => invariants (inv b') ⊓ on_done' b'⌝
      ⊓ spec
        ((inv init).foldr (·⊓·) ⊤)
        (fun b => (inv b).foldr (·⊓·) ⊤ ⊓ on_done' b)
    prop := by
      intro post; simp only [LE.pure]; split_ifs with h <;> try simp
      apply (triple_spec ..).mpr
      simp [invariantGadget, onDoneGadget, decreasingGadget]
      apply MonadNonDet.wp_forIn (inv := fun b => (inv b).foldr (· ⊓ ·) ⊤)
      intro b; apply (wpg b).intro
      solve_by_elim

/- Monad Transformer Algebra for NonDetT -/
noncomputable
scoped
instance [Monad m] [LawfulMonad m] [_root_.CompleteLattice l]
  [inst: MAlgOrdered m l] :
  MAlgLift m l (NonDetT m) l where
    cl := by exact LogicLift.refl
    μ_lift := by
      intros; simp [liftM, monadLift, MonadLift.monadLift, MAlgOrdered.μ, NonDetT.μ, NonDetT.wp,
        pure, wp, MAlg.lift, Functor.map, NonDetT.wp, NonDetT.bind,LogicLift.refl]

end AngelicChoice

end TotalCorrectness
