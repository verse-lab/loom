import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic
import Aesop
import LoL.QuotientExtra
import LoL.Meta
import LoL.MProp.HoareTriples

universe u v w

section NonDetermenisticTransformer

variable {m : Type u -> Type v} {l : Type u} {α β : Type u} [Monad m] [inst: BooleanAlgebra l]

local
instance : SemilatticeInf l := inst.toLattice.toSemilatticeInf

variable  [MPropPartialOrder m l]

structure NonDetT (m : Type u -> Type v) (l : Type u)
  [Monad m] [PartialOrder l] [MPropPartialOrder m l] (α : Type u) where
  tp   : Type w
  pre : tp -> l
  sem  : tp -> m α

@[simp]
lemma meet_pure_true l : min (MProp.pure (m := m) True) l = l := by
  apply le_antisymm <;> simp
  apply MPropPartialOrder.μ_top
@[simp]
lemma pure_true_meet l : min l (MProp.pure (m := m) True) = l := by
  apply le_antisymm <;> simp
  apply MPropPartialOrder.μ_top


def NonDetT.pure (x : α) : NonDetT m l α := ⟨PUnit, fun _ => MProp.pure (m := m) True, fun _ => return x⟩

def NonDetT.bind (x : NonDetT m l α) (f : α → NonDetT m l β) : NonDetT m l β :=
  ⟨
    x.tp × ((out : α) -> (f out).tp),
    fun t => x.pre t.1 ⊓
      pwp (x.sem t.1) fun out => (f out).pre (t.2 out),
    fun t => x.sem t.1 >>= fun out => (f out).sem (t.2 out)
  ⟩

def NonDetT.pick (τ : Type u) : NonDetT m l τ := ⟨τ, fun _ => MProp.pure (m := m) True, Pure.pure⟩

def NonDetT.assume (as : Prop) : NonDetT m l PUnit := ⟨PUnit, fun _ => MProp.pure (m := m) as, fun _ => return .unit⟩

instance : Monad (NonDetT m l) where
  pure := .pure
  bind := .bind

instance : MonadLift m (NonDetT m l) where
  monadLift := fun x => ⟨PUnit, fun _ => MProp.pure (m := m) True, fun _ => x⟩

class MonadInfNonDet (m : Type u → Type v) where
  pick : (τ : Type u) → m τ
  assume : Prop → m PUnit

export MonadInfNonDet (pick assume)

instance : MonadInfNonDet (NonDetT m l) where
  pick   := .pick
  assume := .assume

theorem pick_tp (τ : Type u) : (pick (m := NonDetT m l) τ).tp = τ := rfl
theorem pick_pre (τ : Type u) : (pick (m := NonDetT m l) τ).pre = fun _ => MProp.pure (m := m) True := rfl
theorem assume_tp (as : Prop) : (assume (m := NonDetT m l) as).tp = PUnit := rfl
theorem assume_pre (as : Prop) : (assume (m := NonDetT m l) as).pre = fun _ => MProp.pure (m := m) as := rfl
theorem lift_tp {α : Type u} (x : m α) : (liftM (n := NonDetT m l) x).tp = PUnit := rfl
theorem lift_pre {α : Type u} (x : m α) : (liftM (n := NonDetT m l) x).pre = fun _ => MProp.pure (m := m) True := rfl
theorem lift_sem {α : Type u} (x : m α) : (liftM (n := NonDetT m l) x).sem = fun _ => x := rfl
theorem assume_sem (as : Prop) : (assume (m := NonDetT m l) as).sem = fun _ => return .unit := rfl
theorem pick_sem (τ : Type u) : (pick (m := NonDetT m l) τ).sem = Pure.pure := rfl

instance NonDetT.Setoid (α) : Setoid (NonDetT m l α) where
  r := fun ⟨tp₁, pre₁, sem₁⟩ ⟨tp₂, pre₂, sem₂⟩ =>
    ∃ f : tp₁ -> tp₂,
      f.Bijective ∧
      (∀ t, pre₁ t = pre₂ (f t)) ∧
      (∀ t, sem₁ t = sem₂ (f t))
  iseqv := {
    refl := by
      intro x;
      apply Exists.intro (fun x => x);
      simp;
      exact Function.Involutive.bijective (congrFun rfl)
    symm := by
      intro ⟨tp₁, pred₁, sem₁⟩ ⟨tp₂, pred₂, sem₂⟩ ⟨f, bij, peq, seq⟩; dsimp only
      exists f.surjInv bij.2; constructor
      { refine Function.bijective_iff_has_inverse.mpr ?_; exists f; constructor
        { refine Function.RightInverse.leftInverse ?_
          exact Function.rightInverse_surjInv bij.right }
        refine Function.LeftInverse.rightInverse ?_
        exact Function.leftInverse_surjInv bij }
      simp [peq, seq, Function.surjInv_eq]
    trans := by
      intro ⟨tp₁, pred₁, sem₁⟩ ⟨tp₂, pred₂, sem₂⟩ ⟨tp₃, pred₃, sem₃⟩
        ⟨f₁, bij₁, peq₁, seq₁⟩ ⟨f₂, bij₂, peq₂, seq₂⟩
      simp
      exists (f₂ ∘ f₁); constructor
      { exact Function.Bijective.comp bij₂ bij₁ }
      simp [*] }

lemma bind_eq (x y : NonDetT m l α) {f g : α → NonDetT m l β} :
  x ≈ y ->
  (∀ a, f a ≈ g a) ->
  (x.bind f) ≈ (y.bind g) := by
  rcases x with ⟨tp₁, pre₁, sem₁⟩
  rcases y with ⟨tp₂, pre₂, sem₂⟩
  rintro ⟨r, bij, peq, seq⟩
  simp only [HasEquiv.Equiv, Setoid.r]; intro r
  rcases Classical.skolem.mp r with ⟨fr, fbij⟩; clear r
  unfold NonDetT.bind; dsimp
  exists fun a => ⟨r a.1, fun out => fr out $ a.2 out⟩
  repeat' constructor
  { intro ⟨t₁, fr₁⟩ ⟨t₂, fr₂⟩; simp; intro req
    have req := bij.1 req; subst_vars; simp [funext_iff]
    intro feq out
    solve_by_elim [(fbij out).1.1] }
  { intro ⟨t, gr⟩; rw [@Prod.exists]
    rcases (bij.2 t) with ⟨t', pt'⟩
    exists t'; dsimp; rw [pt']
    simp only [Prod.mk.injEq, true_and, funext_iff]
    apply Classical.skolem (p := fun out bout => fr out bout = gr out) |>.mp
    intro out
    rcases fbij out |>.1.2 (gr out) with ⟨z, pz⟩; exists z }
  { aesop }
  aesop

abbrev LawfullNonDetT m l
  [Monad m] [BooleanAlgebra l] [MPropPartialOrder m l] α :=
  Quotient (NonDetT.Setoid (m := m) α)

-- abbrev LawfullNonDetT.mk : NonDetT m l α -> LawfullNonDetT m l α := Quotient.mk (NonDetT.Setoid α)

def LawfullNonDetT.pure (x : α) : LawfullNonDetT m l α := ⟦NonDetT.pure x⟧

noncomputable def LawfullNonDetT.map
  (f : α → β)
  (x : LawfullNonDetT m l α)
  : LawfullNonDetT m l β :=
  Quotient.liftOn x (⟦f <$> ·⟧)
  (by
    intros; dsimp; apply Quotient.sound
    simp [Functor.map]; apply bind_eq <;> solve_by_elim [Setoid.refl])

noncomputable def LawfullNonDetT.bind
  (x : LawfullNonDetT m l α)
  (f : α → LawfullNonDetT m l β) : LawfullNonDetT m l β :=
  Quotient.liftOn x (⟦Quotient.liftOnFun f ·.bind⟧)
  (by intros; dsimp; apply Quotient.sound
      solve_by_elim [bind_eq, Quotient.liftOnFun_arg])

noncomputable
instance : Functor (LawfullNonDetT m l) where
  map := LawfullNonDetT.map

noncomputable
instance : Monad (LawfullNonDetT m l) where
  pure := LawfullNonDetT.pure
  bind := LawfullNonDetT.bind

instance [LawfulMonad m] : LawfulMonad (LawfullNonDetT m l) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_ (bind_pure_comp := ?_)
  { intros α x
    induction x using Quotient.ind
    rename_i nd; simp only [Functor.map, LawfullNonDetT.map, NonDetT.Setoid]
    simp only [Function.comp_id, Quotient.lift_mk, Quotient.eq]
    exists (·.1); rcases nd with ⟨tp, pre, sem⟩
    simp [NonDetT.bind, NonDetT.pure];
    repeat' constructor <;> try simp
    { rintro ⟨_, _⟩; aesop }
    rintro b; exists ⟨b, fun _ => .unit⟩ }
  { intros α β x f; simp [pure, LawfullNonDetT.pure, bind]
    simp [LawfullNonDetT.bind];
    induction f using Quotient.fun_ind; simp }
  { sorry }
  intros; sorry


instance [LawfulMonad m] : LawfulFunctor (LawfullNonDetT m l) where
  map_const := by intros; rfl
  id_map    := by
    intros α x
    induction x using Quotient.ind
    rename_i nd;
    simp only [Functor.map, LawfullNonDetT.map, NonDetT.Setoid, Function.comp_id, Quotient.lift_mk,
      Quotient.eq]
    rcases nd with ⟨tp, pre, sem⟩
    simp only [NonDetT.bind, NonDetT.pure]; exists (·.1);
    repeat' constructor <;> try simp
    { rintro ⟨_, _⟩; aesop }
    rintro b; exists ⟨b, fun _ => .unit⟩
  comp_map := by
    intros α β γ g h x
    induction x using Quotient.ind; rename_i nd
    simp only [Functor.map, LawfullNonDetT.map, NonDetT.Setoid, Quotient.lift_mk, Quotient.eq]
    rw [Quotient.liftOn_mk]; apply Quotient.sound







instance : Functor (LawfullNonDetT m l) where



notation "NonDetT" t => NonDetT t _


end NonDetermenisticTransformer

section Example

open TotalCorrectness

abbrev myM := NonDetT (StateT Nat (ExceptT String Id))

def ex : myM Unit :=
  do
    set 0
    let x <- get
    assume (x < 1)


example (P : _ -> Prop) : P (ex) := by
  dsimp [ex, bind, pure]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp [pick_tp,
        assume_tp,
        lift_tp,
        assume_pred,
        lift_pred,
        lift_sem,
        assume_sem,
        -bind_pure_comp
        ]
  sorry

def ex' : myM Unit :=
  do
    let x <- pick ℕ
    let y <- pick ℕ
    assume (x < y)
    set (y - x)

example (P : _ -> Prop) : P (ex') := by
  dsimp [ex', bind, pure]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp only [pick_tp,
        assume_tp,
        lift_tp,
        assume_pred,
        lift_pred,
        lift_sem,
        pick_pred,
        pick_sem,
        assume_sem,
        wp_pure,
        meet_pure_true,
        pure_true_meet,
        ]
  sorry


def ex'' : myM Unit :=
  do
    let x <- pick ℕ
    assume (x < 1)
    let y <- pick ℕ
    let s <- get
    assume (y < s)
    set (y - x)

example (P : _ -> Prop) : P (ex'') := by
  dsimp [ex'', bind, pure]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp [pick_tp,
        assume_tp,
        lift_tp,
        assume_pred,
        lift_pred,
        lift_sem,
        pick_sem,
        pick_pred,
        wp_pure,
        assume_sem,
        meet_pure_true,
        pure_true_meet,
        ]
  sorry

#reduce! ex

end Example
