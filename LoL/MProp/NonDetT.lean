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

variable {m : Type u -> Type v} {l : Type u} {α β : Type u} [Monad m] [inst: CompleteBooleanAlgebra l] [MPropOrdered m l]

private lemma join_himp (x y z : l) : x ⊓ y ⇨ z = xᶜ ⊔ (y ⇨ z) := by
  apply le_antisymm
    <;> simp [himp_eq]
    <;> constructor
    <;> solve_by_elim [le_sup_of_le_right, le_sup_of_le_left, le_refl]

open Classical in
private lemma iInf_pi {α} {τ : α -> Type u} (p : (a : α) -> τ a -> l) [inst': ∀ a, Inhabited (τ a)] a :
  ⨅ (t : (α : α) -> τ α), p a (t a) = ⨅ (t : τ a), p a t := by
    apply le_antisymm <;> simp
    { intro i;
      refine iInf_le_of_le (fun x =>
        if h : x = a then by rw [h]; exact i else (inst' x).default) ?_
      simp }
    intro i; apply iInf_le_of_le (i a); simp

structure NonDet (m : Type u -> Type v) (l : Type u) (α : Type u) where
  tp  : Type u
  inh : Inhabited tp
  pre : tp -> l
  sem : tp -> m α

structure NonDetCps (m : Type u -> Type v) (l : Type u) (α : Type u) where
  tpc : (α -> Type u) -> Type u
  pre {τ : α -> Type u}              (cont : (a : α) -> τ a -> l)   : tpc τ -> l
  sem {τ : α -> Type u} {β : Type u} (cont : (a : α) -> τ a -> m β) : tpc τ -> m β

structure NonDetT (m : Type u -> Type v) {l : Type u} [Monad m] [CompleteBooleanAlgebra l] [MPropOrdered m l] (α : Type u)
  extends NonDetCps m l α where
  inh (τ : α -> Type u) : (∀ a, Inhabited (τ a)) -> Inhabited (tpc τ)
  pre_sem {τ τ' : α -> Type u} {_ : ∀ a, Inhabited (τ a)} { _ : ∀ a, Inhabited (τ' a)}
    (cp₁ : (a : α) -> τ a -> l) (cp₂ : (a : α) -> τ' a -> l)
    (cs₁ : (a : α) -> τ a -> m UProp) (cs₂ : (a : α) -> τ' a -> m UProp) :
    (∀ a, ⨅ t,  cp₁ a t ⇨ MProp.μ (cs₁ a t) <= ⨅ t, cp₂ a t ⇨ MProp.μ (cs₂ a t)) ->
    ⨅ t, pre cp₁ t ⇨ MProp.μ (sem cs₁ t) <=
    ⨅ t, pre cp₂ t ⇨ MProp.μ (sem cs₂ t)
  sem_bind {τ : α -> Type u} {β γ} (t : tpc τ)
    (cont : (a : α) -> τ a -> m β)
    (cont' : β -> m γ) :
    sem cont t >>= cont' = sem (cont · · >>= cont') t

@[simp]
def NonDetT.finally (x : NonDetT m α) : NonDet m l α := {
  tp := x.tpc (fun _ => PUnit)
  inh := x.inh (fun _ => PUnit) (fun _ => ⟨.unit⟩)
  pre := fun t => x.pre ⊤ t
  sem := fun t => x.sem (fun _ => Pure.pure ·) t
}

def NonDetT.tp (x : NonDetT m α) := x.finally.tp

@[simp]
def NonDet.run (x : NonDet m l α) (seed : x.tp) := x.sem seed
def NonDetT.run (x : NonDetT m α) (seed : x.tp) := x.finally.run seed
@[simp]
def NonDet.seed (x : NonDet m l α) := x.inh.default
def NonDetT.seed (x : NonDetT m α) := x.finally.seed

def NonDetT.any (x : NonDetT m α) : m α := x.run x.seed

@[simp]
def NonDet.validSeed (x : NonDet m l α) (pre : l) (seed : x.tp) := pre ≤ x.pre seed
def NonDetT.validSeed (x : NonDetT m α) (pre : l) (seed : x.tp) := x.finally.validSeed pre seed

@[simp]
def NonDet.μ (x : NonDet m l UProp) : l :=  ⨅ t : x.tp, x.pre t ⇨ MProp.μ (x.sem t)

def NonDetT.μ (x : NonDetT m UProp) : l := x.finally.μ

variable [MPropDetertministic m l] [LawfulMonad m]

def NonDetT.pure (x : α) : NonDetT m α := {
  tpc τ := τ x
  pre cont := cont x
  sem cont := cont x

  inh τ inh := by solve_by_elim
  pre_sem := by introv _ _ h; simp only [h]
  sem_bind := by introv; simp
}

def NonDetT.bind (x : NonDetT m α) (f : α → NonDetT m β) : NonDetT m β := {
  tpc τ := x.tpc <| fun out => (f out).tpc τ
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

def NonDetT.pick (α : Type u) [Inhabited α] : NonDetT m α := {
  tpc τ := (a : α) × τ a
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

def NonDetT.assume  (as : Prop) : NonDetT m PUnit := {
  tpc τ := τ .unit
  sem cont t := cont .unit t
  pre cont t := ⌜as⌝ ⊓ cont .unit t

  inh τ inh := by solve_by_elim
  pre_sem := by
    introv _ _; simp only [join_himp]
    rw [←sup_iInf_eq, ←sup_iInf_eq];
    exact fun a ↦ sup_le_sup_left (a PUnit.unit) ⌜as⌝ᶜ
  sem_bind := by simp
}

instance : Monad (NonDetT m) where
  pure := .pure
  bind := .bind

class MonadNonDet (m : Type u → Type v) where
  pick : (τ : Type u) -> [Inhabited τ] → m τ
  assume : Prop → m PUnit

export MonadNonDet (pick assume)

instance : MonadNonDet (NonDetT m) where
  pick   := .pick
  assume := .assume

instance : MonadLift m (NonDetT m) where
  monadLift {α} c := {
    tpc τ := (a : α) -> τ a
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

instance : LawfulMonad (NonDetT m) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_ <;> (intros; rfl)

instance : MPropOrdered (NonDetT m) l := {
  μ := NonDetT.μ
  ι := fun p => monadLift (m := m) (MProp.ι p)
  μ_surjective := by intro p; simp [NonDetT.μ, monadLift, MonadLift.monadLift]; rw [MPropOrdered.μ_surjective]; rw [@iInf_const]
  μ_top := by intro x; simp [NonDetT.μ, pure, NonDetT.pure]; apply MPropOrdered.μ_top
  μ_bot := by intro x; simp [NonDetT.μ, pure, NonDetT.pure, iInf_const]; apply MPropOrdered.μ_bot
  μ_ord_pure := by
    intro p₁ p₂ h; simp [NonDetT.μ, pure, NonDetT.pure, iInf_const]; apply MPropOrdered.μ_ord_pure
    assumption
  μ_ord_bind := by
    intro α f g
    simp [Function.comp, Pi.hasLe, Pi.partialOrder, Pi.preorder, inferInstanceAs]
    intros le x
    simp [liftM, monadLift, MonadLift.monadLift, bind, NonDetT.bind, NonDetT.pure]
    simp only [NonDetT.μ]
    apply x.pre_sem
    { solve_by_elim }
    { intro a; solve_by_elim [(f a).inh] }
    intro a; solve_by_elim [(g a).inh]
  }

section NonDetTSimplifications

theorem lift_tpc {α : Type u} (x : m α) :
  (liftM (n := NonDetT m) x).tpc = ((a : α) -> · a) := rfl
theorem lift_pre {α : Type u} τ (x : m α) :
  (liftM (n := NonDetT m) x).pre (τ := τ)  =
  fun cont t => wlp x fun a => cont a (t a) := rfl
theorem lift_sem {α β : Type u} τ (x : m α) :
  (liftM (n := NonDetT m) x).sem (β := β) (τ := τ) = fun cont t => x >>= fun a => cont a (t a) := rfl

omit [LawfulMonad m] [MPropDetertministic m l]
theorem pick_tpc (τ : Type u) [Inhabited τ] :
  (pick (m := NonDetT m) τ).tpc = ((t : τ) × · t) := rfl
theorem pick_pre (τ : Type u) τ' [Inhabited τ] :
  (pick (m := NonDetT m) τ).pre (τ := τ') =
  (fun cont t => cont t.1 t.2) := rfl
theorem assume_tpc (as : Prop) : (assume (m := NonDetT m) as).tpc = (· .unit) := rfl
theorem assume_pre τ (as : Prop) :
  (assume (m := NonDetT m) as).pre (τ := τ) =
  fun cont t => ⌜as⌝ ⊓ cont .unit t := rfl
theorem assume_sem τ (as : Prop) :
  (assume (m := NonDetT m) as).sem (β := β) (τ := τ) =
  fun cont t => cont .unit t := rfl
theorem pick_sem (τ : Type u) [Inhabited τ] τ' :
  (pick (m := NonDetT m) τ).sem (β := β) (τ := τ') =
  fun cont t => cont t.1 t.2 := rfl

end NonDetTSimplifications

lemma NonDetT.wp_eq (c : NonDetT m α) post :
  wp c post =
    ⨅ t : c.tpc (fun _ => PUnit),
      c.pre ⊤ t ⇨ wp (c.sem (fun _ => Pure.pure ·) t) post := by
   simp [wp, liftM, monadLift, MProp.lift, MProp.μ, MPropOrdered.μ]
   simp [NonDetT.μ, bind, NonDetT.bind, MProp.ι, MPropOrdered.ι]
   simp [monadLift, MonadLift.monadLift]
   simp [c.sem_bind, MProp.μ]; apply le_antisymm
   { apply c.pre_sem <;> (try simp [iInf_const]) <;> solve_by_elim }
   apply c.pre_sem <;> (try simp [iInf_const]) <;> solve_by_elim

lemma MonadNonDet.wp_pick (τ : Type u) [Inhabited τ] (post : τ -> l) :
  wp (pick (m := NonDetT m) τ) post = ⨅ t, post t := by
    simp [NonDetT.wp_eq, pick_pre, pick_sem, wp_pure, pick_tpc]
    apply le_antisymm <;> simp <;> intro i
    { apply iInf_le_of_le ⟨i, .unit⟩; simp }
    apply iInf_le_of_le i.fst; simp

lemma MonadNonDet.wp_assume as (post : PUnit -> l) :
  wp (assume (m := NonDetT m) as) post = ⌜as⌝ ⇨ post .unit := by
    simp [NonDetT.wp_eq, pick_pre,wp_pure, assume_sem, assume_pre, assume_tpc]
    apply le_antisymm
    { apply iInf_le_of_le .unit; simp }
    simp

lemma NonDetT.lift (c : m α) post :
  wp (liftM (n := NonDetT m) c) post = wp c post := by
    simp [NonDetT.wp_eq, pick_pre, wp_pure, lift_sem, lift_pre, lift_tpc]
    apply le_antisymm
    { apply iInf_le_of_le (fun _ => .unit); simp }
    simp

lemma NonDetT.run_validSeed (x : NonDetT m α) (pre : l) (post : α -> l) (seed : x.tp) :
  x.validSeed pre seed ->
  triple pre x post ->
  triple pre (x.run seed) post := by
    simp [NonDetT.validSeed, triple, NonDetT.run, NonDetT.wp_eq]
    intro v h; apply le_trans'; apply h; simp [v]

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
  dsimp [ex, bind, pure, NonDetT.finally]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp [pick_tpc,
        assume_tpc,
        lift_tpc,
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
  dsimp [ex', bind, pure, NonDetT.finally]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
  simp only [pick_tpc,
        assume_tpc,
        lift_tpc,
        assume_pre,
        lift_pre,
        lift_sem,
        pick_pre,
        pick_sem,
        assume_sem,
        wp_pure,
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
  dsimp [ex'', bind, pure, NonDetT.finally]
  unfold NonDetT.bind;
  simp [set, get, getThe, MonadStateOf.get]
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
        Id
        ]
  sorry

end Example
