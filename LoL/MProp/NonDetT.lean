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

variable {m : Type u -> Type v} {l : Type u} {α β : Type u} [Monad m] [inst: CompleteBooleanAlgebra l]

local
instance : SemilatticeInf l := inst.toLattice.toSemilatticeInf

variable  [MPropPartialOrder m l]

structure NonDetT' (m : Type u -> Type v) (l : Type u)
  [Monad m] [CompleteBooleanAlgebra l] [MPropPartialOrder m l] [MPropDetertministic m l]
  (α : Type u) where
  tp   : (α -> Type u) -> Type u
  pre {τ : α -> Type u} (cont : (a : α) -> τ a -> l) : tp τ -> l
  sem {τ : α -> Type u} {β : Type u} (cont : (a : α) -> τ a -> m β) : tp τ -> m β

  inh (τ : α -> Type u) : (∀ a, Inhabited (τ a)) -> Inhabited (tp τ)
  pre_sem {τ τ' : α -> Type u} {_ : ∀ a, Inhabited (τ a)} { _ : ∀ a, Inhabited (τ' a)}
    (cp₁ : (a : α) -> τ a -> l) (cp₂ : (a : α) -> τ' a -> l)
    (cs₁ : (a : α) -> τ a -> m UProp) (cs₂ : (a : α) -> τ' a -> m UProp) :
    (∀ a, ⨅ t,  cp₁ a t ⇨ MProp.μ (cs₁ a t) <= ⨅ t, cp₂ a t ⇨ MProp.μ (cs₂ a t)) ->
    ⨅ t, pre cp₁ t ⇨ MProp.μ (sem cs₁ t) <=
    ⨅ t, pre cp₂ t ⇨ MProp.μ (sem cs₂ t)
  sem_bind {τ : α -> Type u} {β γ} (t : tp τ)
    (cont : (a : α) -> τ a -> m β)
    (cont' : β -> m γ) :
    sem cont t >>= cont' = sem (cont · · >>= cont') t

@[simp]
lemma meet_pure_true l : min (MProp.pure (m := m) True) l = l := by simp
@[simp]
lemma pure_true_meet l : min l (MProp.pure (m := m) True) = l := by simp

variable [MPropDetertministic m l] [LawfulMonad m]

def NonDetT'.pure (x : α) : NonDetT' m l α := {
  tp τ := τ x
  pre cont := cont x
  sem cont := cont x

  inh τ inh := by solve_by_elim
  pre_sem := by introv _ _ h; simp only [h]
  sem_bind := by introv; simp
}

def NonDetT'.bind (x : NonDetT' m l α) (f : α → NonDetT' m l β) : NonDetT' m l β := {
  tp τ := x.tp <| fun out => (f out).tp τ
  sem cont := x.sem fun a ft => (f a).sem cont ft
  pre cont := x.pre fun a ft => (f a).pre cont ft

  inh τ inh := by
    simp; apply x.inh; intro a; apply (f a).inh; exact inh
  pre_sem := by
    introv _ _ h; simp only
    apply x.pre_sem <;> intro a <;> solve_by_elim [(f a).pre_sem, (f a).inh]
  sem_bind := by
    introv; simp [x.sem_bind, (f _).sem_bind];
}


def NonDetT'.pick (α : Type u) [Inhabited α] : NonDetT' m l α := {
  tp τ := (a : α) × τ a
  sem cont t := cont t.1 t.2
  pre cont t := cont t.1 t.2

  inh τ inh := by
    simp; exists default; apply (inh default).default
  pre_sem := by
    introv _ _; simp; rintro h ⟨a, t⟩; simp
    apply le_trans'; apply h
    simp; intro t
    rw [<-le_himp_iff, <-le_himp_iff]
    refine iInf_le_of_le ⟨a, t⟩ ?_
    exact le_himp
  sem_bind := by simp
}

private lemma join_himp (x y z : l) : x ⊓ y ⇨ z = xᶜ ⊔ (y ⇨ z) := by
  apply le_antisymm
    <;> simp [himp_eq]
    <;> constructor
    <;> solve_by_elim [le_sup_of_le_right, le_sup_of_le_left, le_refl]


def NonDetT'.assume  (as : Prop) : NonDetT' m l PUnit := {
  tp τ := τ .unit
  sem cont t := cont .unit t
  pre cont t := ⌜as⌝ ⊓ cont .unit t

  inh τ inh := by solve_by_elim
  pre_sem := by
    introv _ _; simp only [join_himp]
    rw [←sup_iInf_eq, ←sup_iInf_eq];
    exact fun a ↦ sup_le_sup_left (a PUnit.unit) ⌜as⌝ᶜ
  sem_bind := by simp
}

instance : Monad (NonDetT' m l) where
  pure := .pure
  bind := .bind

open Classical in
private lemma iInf_pi {α} {τ : α -> Type u} (p : (a : α) -> τ a -> l) [inst': ∀ a, Inhabited (τ a)] a :
  ⨅ (t : (α : α) -> τ α), p a (t a) = ⨅ (t : τ a), p a t := by
    apply le_antisymm <;> simp
    { intro i;
      refine iInf_le_of_le (fun x =>
        if h : x = a then by rw [h]; exact i else (inst' x).default) ?_
      simp }
    intro i; apply iInf_le_of_le (i a); simp


instance : MonadLift m (NonDetT' m l) where
  monadLift {α} c := {
    tp τ := (a : α) -> τ a
    pre cont t := wlp c fun a => cont a (t a)
    sem cont t := c >>= fun a => cont a (t a)

    inh τ inh := by
      simp; exact ⟨fun a => inh a |>.default⟩
    pre_sem := by
      introv h _ _; simp only
      simp only [μ_bind_wp (m := m), <-wlp_himp, Function.comp_apply]
      rw [<-wp_iInf, <-wp_iInf]; apply wp_cons; intro y
      rw [iInf_pi (a := y) (p := fun y iy => cp₁ y iy ⇨ MProp.μ (m := m) (cs₁ y iy))]
      rw [iInf_pi (a := y) (p := fun y iy => cp₂ y iy ⇨ MProp.μ (m := m) (cs₂ y iy))]
      solve_by_elim
    sem_bind := by simp
  }

class MonadInfNonDet (m : Type u → Type v) where
  pick : (τ : Type u) -> [Inhabited τ] → m τ
  assume : Prop → m PUnit

export MonadInfNonDet (pick assume)

instance : MonadInfNonDet (NonDetT' m l) where
  pick   := .pick
  assume := .assume


instance : LawfulMonad (NonDetT' m l) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_ <;> (intros; rfl)

def NonDetT'.μ (x : NonDetT' m l UProp) : l :=
  ⨅ t : x.tp (fun _ => PUnit),
    x.pre (fun _ _ => ⊤) t ⇨ MProp.μ (x.sem (fun a _ => Pure.pure a) t)

instance [LawfulMonad m] : MPropPartialOrder (NonDetT' m l) l := {
  μ := NonDetT'.μ
  ι := fun p => monadLift (m := m) (MProp.ι p)
  μ_surjective := by intro p; simp [NonDetT'.μ, monadLift, MonadLift.monadLift]; rw [MProp.μ_surjective]; rw [@iInf_const]
  μ_top := by intro x; simp [NonDetT'.μ, pure, NonDetT'.pure]; apply MPropPartialOrder.μ_top
  μ_bot := by intro x; simp [NonDetT'.μ, pure, NonDetT'.pure, iInf_const]; apply MPropPartialOrder.μ_bot
  μ_ord_pure := by
    intro p₁ p₂ h; simp [NonDetT'.μ, pure, NonDetT'.pure, iInf_const]; apply MPropPartialOrder.μ_ord_pure
    assumption
  μ_ord_bind := by
    intro α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]
    intros le x
    simp [liftM, monadLift, MonadLift.monadLift, bind, NonDetT'.bind, NonDetT'.pure]
    simp only [NonDetT'.μ]
    apply x.pre_sem
    { solve_by_elim }
    { intro a; solve_by_elim [(f a).inh] }
    intro a; solve_by_elim [(g a).inh]
  }

omit [LawfulMonad m]
theorem pick_tp (τ : Type u) [Inhabited τ] :
  (pick (m := NonDetT' m l) τ).tp = ((t : τ) × · t) := rfl
theorem pick_pre (τ : Type u) τ' [Inhabited τ] :
  (pick (m := NonDetT' m l) τ).pre (τ := τ') =
  (fun cont t => cont t.1 t.2) := rfl
theorem assume_tp (as : Prop) : (assume (m := NonDetT' m l) as).tp = (· .unit) := rfl
theorem assume_pre τ (as : Prop) :
  (assume (m := NonDetT' m l) as).pre (τ := τ) =
  fun cont t => ⌜as⌝ ⊓ cont .unit t := rfl
theorem lift_tp {α : Type u} (x : m α) [LawfulMonad m] :
  (liftM (n := NonDetT' m l) x).tp = ((a : α) -> · a) := rfl
theorem lift_pre {α : Type u} τ (x : m α) [LawfulMonad m] :
  (liftM (n := NonDetT' m l) x).pre (τ := τ)  =
  fun cont t => wlp x fun a => cont a (t a) := rfl
theorem lift_sem {α β : Type u} τ (x : m α) [LawfulMonad m] :
  (liftM (n := NonDetT' m l) x).sem (β := β) (τ := τ) = fun cont t => x >>= fun a => cont a (t a) := rfl
theorem assume_sem τ (as : Prop) :
  (assume (m := NonDetT' m l) as).sem (β := β) (τ := τ) =
  fun cont t => cont .unit t := rfl
theorem pick_sem (τ : Type u) [Inhabited τ] τ' [LawfulMonad m] :
  (pick (m := NonDetT' m l) τ).sem (β := β) (τ := τ') =
  fun cont t => cont t.1 t.2 := rfl

notation:max "NonDetT" m:max => NonDetT' (l := _) m

lemma NonDetT_wp_eq [LawfulMonad m] (c : NonDetT m α) post :
  wp c post =
    ⨅ t : c.tp (fun _ => PUnit),
      c.pre ⊤ t ⇨ wp (c.sem (fun _ => pure ·) t) post := by
   simp [wp, liftM, monadLift, MProp.lift, MProp.μ, MPropPartialOrder.μ]
   simp [NonDetT'.μ, bind, NonDetT'.bind, MProp.ι, MPropPartialOrder.ι]
   simp [monadLift, MonadLift.monadLift]
   simp [c.sem_bind, MProp.μ]; apply le_antisymm
   { apply c.pre_sem <;> (try simp [iInf_const]) <;> solve_by_elim }
   apply c.pre_sem <;> (try simp [iInf_const]) <;> solve_by_elim

structure NonDetFinall (m : Type u -> Type v) (l : Type u) (α : Type u) where
  tp : Type u
  protected choose : tp
  pre : tp -> l
  sem : tp -> m α

def NonDetT'.finally (x : NonDetT' m l α) : NonDetFinall m l α := {
  tp := x.tp (fun _ => PUnit)
  choose := x.inh (fun _ => PUnit) (fun _ => ⟨.unit⟩) |>.default
  pre := fun t => x.pre ⊤ t
  sem := fun t => x.sem (fun _ => Pure.pure ·) t
}

def NonDetT'.any (x : NonDetT' m l α) : m α := do
  let xf := x.finally; xf.sem xf.choose

lemma NonDetT'.wp_pick [LawfulMonad m] (τ : Type u) [Inhabited τ] (post : τ -> l) :
  wp (MonadInfNonDet.pick (m := NonDetT' m l) τ) post = ⨅ t, post t := by
    simp [NonDetT_wp_eq, pick_pre, pick_sem, wp_pure, pick_tp]
    apply le_antisymm <;> simp <;> intro i
    { apply iInf_le_of_le ⟨i, .unit⟩; simp }
    apply iInf_le_of_le i.fst; simp

lemma NonDetT'.wp_assume [LawfulMonad m] as (post : PUnit -> l) :
  wp (MonadInfNonDet.assume (m := NonDetT' m l) as) post = ⌜as⌝ ⇨ post .unit := by
    simp [NonDetT_wp_eq, pick_pre,wp_pure, assume_sem, assume_pre, assume_tp]
    apply le_antisymm
    { apply iInf_le_of_le .unit; simp }
    simp

lemma NonDetT'.lift [LawfulMonad m] (c : m α) post :
  wp (liftM (n := NonDetT' m l) c) post = wp c post := by
    simp [NonDetT_wp_eq, pick_pre, wp_pure, lift_sem, lift_pre, lift_tp]
    apply le_antisymm
    { apply iInf_le_of_le (fun _ => .unit); simp }
    simp



end NonDetermenisticTransformer

section Example

open TotalCorrectness

abbrev myM := NonDetT (StateT Nat (ExceptT String Id))

def ex : myM Unit :=
  do
    set 0
    let x <- get
    assume (x < 1)


example (P : _ -> Prop) : P (ex.finally) := by
  dsimp [ex, bind, pure, NonDetT'.finally]
  unfold NonDetT'.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp [pick_tp,
        assume_tp,
        lift_tp,
        assume_pre,
        lift_pre,
        lift_sem,
        assume_sem,
        -bind_pure_comp,
        Id
        ]
  sorry

def ex' : myM Unit :=
  do
    let x <- pick ℕ
    let y <- pick ℕ
    assume (x < y)
    set (y - x)

example (P : _ -> Prop) : P (ex'.finally) := by
  dsimp [ex', bind, pure, NonDetT'.finally]
  unfold NonDetT'.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp only [pick_tp,
        assume_tp,
        lift_tp,
        assume_pre,
        lift_pre,
        lift_sem,
        pick_pre,
        pick_sem,
        assume_sem,
        wp_pure,
        meet_pure_true,
        pure_true_meet,
        Id
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

example (P : _ -> Prop) : P (ex''.finally) := by
  dsimp [ex'', bind, pure, NonDetT'.finally]
  unfold NonDetT'.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp [pick_tp,
        assume_tp,
        lift_tp,
        assume_pre,
        lift_pre,
        lift_sem,
        pick_sem,
        pick_pre,
        wp_pure,
        assume_sem,
        meet_pure_true,
        pure_true_meet,
        Id
        ]
  sorry

end Example
