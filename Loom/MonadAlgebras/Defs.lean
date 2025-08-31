import Mathlib.Order.CompleteLattice.Basic

import Loom.MonadUtil
import Loom.SpecMonad

universe u v w

/- Prop embedding into PartialOrder -/

open Classical in
noncomputable def LE.pure {l : Type u} [inst: LE l] [OrderTop l] [OrderBot l] : Prop -> l := fun p =>
  if p then ⊤ else ⊥

macro "⌜" p:term "⌝" : term => `(LE.pure $p)

@[app_unexpander LE.pure] def unexpandPure : Lean.PrettyPrinter.Unexpander
  | `($(_) $p:term) => `(⌜$p:term⌝)
  | _ => throw ()

@[simp]
lemma trueE (l : Type v) [inst: LE l] [OrderTop l] [OrderBot l] : ⌜True⌝ = (⊤ : l) := by
  simp [LE.pure]

@[simp]
lemma falseE (l : Type v) [inst: LE l] [OrderTop l] [OrderBot l] : ⌜False⌝ = (⊥ : l) := by
  simp [LE.pure]

open Classical in
lemma LE.pure_imp {l : Type u} [inst: LE l] [OrderTop l] [OrderBot l]
  (p₁ p₂ : Prop) : (p₁ -> p₂) -> ⌜p₁⌝ <= (⌜p₂⌝ : l) := by
  simp [LE.pure]; split <;> aesop

@[simp]
lemma LE.pure_intro {l : Type u} [inst: LE l] [OrderTop l] [OrderBot l]
  (p : Prop) (h : l) : (⌜p⌝ <= h) = (p -> ⊤ <= h) := by
    simp [LE.pure]; split <;> aesop

@[simp]
lemma pure_intro_l {l : Type u} [CompleteLattice l] (x y : l) :
  (x ⊓ ⌜ p ⌝ <= y) = (p -> x <= y) := by
  by_cases h : p <;> simp [h, trueE, falseE]

@[simp]
lemma pure_intro_r {l : Type u} [CompleteLattice l] (x y : l) :
  (⌜ p ⌝ ⊓ x <= y) = (p -> x <= y) := by
  by_cases h : p <;> simp [h, trueE, falseE]

variable (m : Type v -> Type u)

class MAlg [Monad m] (l : outParam (Type v)) where
  μ : m l -> l
  pure : ∀ l, μ (pure l) = l
  bind : ∀ {α : Type v} (x : m α) (f g : α -> m l),
    μ ∘ f = μ ∘ g ->
    μ (x >>= f) = μ (x >>= g)

abbrev MAlg.lift {m : Type u -> Type v} {l : Type u} [Monad m] [MAlg m l] :
  {α : Type u} -> m α -> Cont l α := fun x f => μ $ f <$> x

instance (l : Type u) {m : Type u -> Type v} [Monad m] [MAlg m l] : MonadLiftT m (Cont l) where
  monadLift := MAlg.lift

instance EffectObservationOfMAlg (l : Type u) {m : Type u -> Type v} [Monad m] [LawfulMonad m] [MAlg m l] : LawfulMonadLiftT m (Cont l) where
  monadLift_pure := by
    intro α x; simp [monadLift, pure]; unfold MAlg.lift; simp [map_pure, MAlg.pure]
  monadLift_bind := by
    intros α β x f; simp [monadLift, bind]; unfold MAlg.lift; ext g
    rw (config := { occs := .pos [2] }) [map_eq_pure_bind]
    simp only [map_bind]; apply MAlg.bind
    ext; simp [MAlg.pure]

class MAlgOrdered (l : outParam (Type v)) [Monad m] [CompleteLattice l] where
  μ : m l -> l
  μ_ord_pure : ∀ l, μ (pure l) = l
  μ_ord_bind {α : Type v} :
    ∀ (f g : α -> m l), μ ∘ f ≤ μ ∘ g ->
      ∀ x : m α, μ (x >>= f) ≤ μ (x >>= g)

instance OfMAlgPartialOrdered {m : Type u -> Type v} {l : Type u} [Monad m] [CompleteLattice l] [mprop : MAlgOrdered m l] : MAlg m l where
  μ := MAlgOrdered.μ
  pure := MAlgOrdered.μ_ord_pure
  bind := by intros; apply PartialOrder.le_antisymm
    <;> apply MAlgOrdered.μ_ord_bind
    <;> simp_all only [le_refl]

lemma MAlgOrdered.bind {α : Type u} {m} {l : Type u} [Monad m] [CompleteLattice l] [MAlgOrdered m l] :
    ∀ (x : m α) (f g : α -> m l), μ ∘ f = μ ∘ g ->
     μ (x >>= f) = μ (x >>= g) := MAlg.bind

lemma Cont.monotone_lift {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteLattice l] [MAlgOrdered m l] :
  ∀ {α : Type u} (x : m α), MAlg.lift x |>.monotone := by
  unfold Cont.monotone; intros; simp [MAlg.lift]; rw [map_eq_pure_bind, map_eq_pure_bind]
  apply MAlgOrdered.μ_ord_bind; intro; simp [MAlgOrdered.μ_ord_pure, *]

@[simp]
lemma MAlg.μ_eq {m l} [Monad m] [CompleteLattice l] [MAlgOrdered m l] : MAlg.μ (m := m) = MAlgOrdered.μ (m := m) := by rfl

lemma MAlg.monadLift_bind {α β} {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteLattice l] [MAlgOrdered m l]
  (x : m α) (f g : α -> Cont l β) :
    f <= g ->
    (lift x >>= f) ≤ (lift x >>= g) := by
    intro fLg h; simp [Bind.bind]
    apply Cont.monotone_lift; intros h; apply fLg

/-- Class for deterministic monadic algebras -/
class MAlgDet (l : outParam (Type v)) [Monad m] [CompleteLattice l] [MAlgOrdered m l] where
  /-- Demonic determinism -/
  demonic {α ι : Type v} (c : m α) (p : ι -> α -> l) [Nonempty ι] :
    ⨅ i, MAlg.lift c (p i) ≤ MAlg.lift c (fun x => ⨅ i, p i x)
  /-- Angelic determinism -/
  angelic {α ι : Type v} (c : m α) (p : ι -> α -> l) [Nonempty ι] :
    ⨆ i, MAlg.lift c (p i) ≥ MAlg.lift c (fun x => ⨆ i, p i x)

/-- Class for partial correctness monadic algebras -/
class MAlgPartial (m : Type u -> Type v) [Monad m] [∀ α, Lean.Order.CCPO (m α)]
  [CompleteLattice l] [MAlgOrdered m l] where
  csup_lift {α : Type u} (xc : Set (m α)) (post : α -> l) :
    Lean.Order.chain xc ->
    ⨅ x ∈ xc, MAlg.lift x post <= MAlg.lift (Lean.Order.CCPO.csup xc) post

/-- Class for total correctness monadic algebras -/
class MAlgTotal (m : Type u -> Type v) [Monad m] [∀ α, Lean.Order.CCPO (m α)]
  [CompleteLattice l] [MAlgOrdered m l] where
  bot_lift {α : Type u} (post : α -> l) :
    MAlg.lift (Lean.Order.bot : m α) post <= ⊥

class NoFailure (m : Type u -> Type v) [Monad m] [CompleteLattice l] [MAlgOrdered m l] where
  noFailure {α : Type u} (c : m α) :
    MAlg.lift c (fun _ => ⊤) = ⊤

class LogicLiftT (l : (Type u)) ( k : Type u) [CompleteLattice l] [CompleteLattice k] where
  [lift : MonadLiftT (Cont l) (Cont k)]
  lift_top {α : Type u} :
    monadLift (m := Cont l) (n := Cont k) (fun (_ : α -> l) => ⊤) = ⊤
  lift_bot {α : Type u} :
    monadLift (m := Cont l) (n := Cont k) (fun (_ : α -> l) => ⊥) = ⊥

class LogicLift (l : outParam (Type u)) ( k : Type u) [CompleteLattice l] [CompleteLattice k] where
  [lift : MonadLift (Cont l) (Cont k)]
  lift_top {α : Type u} :
    monadLift (m := Cont l) (n := Cont k) (fun (_ : α -> l) => ⊤) = ⊤
  lift_bot {α : Type u} :
    monadLift (m := Cont l) (n := Cont k) (fun (_ : α -> l) => ⊥) = ⊥

def LogicLift.refl [CompleteLattice l] : LogicLift l l where
  lift := by exact ⟨id⟩
  lift_top := rfl
  lift_bot := rfl


instance [CompleteLattice l] [CompleteLattice k] [LogicLiftT l k] : MonadLiftT (Cont l) (Cont k) where
  monadLift := LogicLiftT.lift.monadLift

instance [CompleteLattice l] [CompleteLattice k] [LogicLift l k] : MonadLift (Cont l) (Cont k) where
  monadLift := LogicLift.lift.monadLift


@[simp]
lemma lift_cont_eq {l σ : Type u} [CompleteLattice l] [CompleteLattice σ] (c : Cont l α) :
  liftM (m := Cont l) (n := Cont (σ -> l)) c = fun post s => c (post · s)  := by
    rfl

instance {l} [CompleteLattice l] : LogicLiftT l l where
  lift_top := by simp [liftM, monadLift, MonadLift.monadLift]; intros; rfl
  lift_bot := by simp [liftM, monadLift, MonadLift.monadLift]; intros; rfl

instance [CompleteLattice l] [CompleteLattice k] [CompleteLattice p] [linst₁ : LogicLiftT l k] [linst₂ : LogicLift k p] : LogicLiftT l p where
  lift_top := by
    simp [instMonadLiftTOfMonadLift, liftM]; intro
    have : (monadLift (m := Cont l) (n := Cont k) (fun (_ : _ -> l) => ⊤)) = ⊤ := by {
      apply linst₁.lift_top
      assumption }
    rw [this]
    apply linst₂.lift_top
  lift_bot := by
    simp [instMonadLiftTOfMonadLift, liftM]; intro
    have : (monadLift (m := Cont l) (n := Cont k) (fun (_ : _ -> l) => ⊥)) = ⊥ := by {
      apply linst₁.lift_bot
      assumption }
    rw [this]
    apply linst₂.lift_bot


instance {l σ : Type u} [CompleteLattice l] : LogicLift l (σ -> l) where
  lift_top := by simp [liftM, monadLift, MonadLift.monadLift]; intros; rfl
  lift_bot := by simp [liftM, monadLift, MonadLift.monadLift]; intros; rfl


class MAlgLift
  (m : semiOutParam (Type u -> Type v)) (l : semiOutParam (Type u)) [Monad m] [CompleteLattice l] [MAlgOrdered m l]
  (n : (Type u -> Type w)) (k : outParam (Type u)) [Monad n] [CompleteLattice k] [MAlgOrdered n k]
  [MonadLiftT m n]
  where
    [cl : LogicLift l k]
    μ_lift (x : m α) : MAlg.lift (liftM (n := n) x) f = liftM (n := Cont k) (MAlg.lift x) f

def MAlgLift.mk_rep  (m : semiOutParam (Type u -> Type v)) (l : semiOutParam (Type u)) [Monad m] [CompleteLattice l] [MAlgOrdered m l]
  (n : (Type u -> Type w)) (σ : Type u) [LawfulMonad m] [Monad n] [LawfulMonad n] [CompleteLattice k] [MAlgOrdered n (σ -> l)]
  [MonadLiftT m n] [LawfulMonadLiftT m n]
  (μ_lift : ∀ (x : m (σ → l)),
    MAlgOrdered.μ (liftM (n := n) x) =
    fun s => MAlgOrdered.μ ((· s) <$> x)) : MAlgLift m l n (σ → l) := by
    constructor; intro α f x
    simp [MAlg.lift]; rw [←lift_map]
    rw [μ_lift (f <$> x)]
    simp [Functor.map_map]

def MAlgLift.mk_id  (m : semiOutParam (Type u -> Type v)) (l : semiOutParam (Type u)) [Monad m] [CompleteLattice l] [MAlgOrdered m l]
  (n : (Type u -> Type w)) [LawfulMonad m] [Monad n] [LawfulMonad n] [CompleteLattice k] [MAlgOrdered n l]
  [MonadLiftT m n] [LawfulMonadLiftT m n]
  (μ_lift : ∀ (x : m l),
    MAlgOrdered.μ (liftM (n := n) x) =
    MAlgOrdered.μ x) : MAlgLift m l n l := by
    let cl := LogicLift.refl (l := l)
    constructor; intro α f x
    simp [MAlg.lift]; rw [<-lift_map]; apply μ_lift

class MAlgLiftT
  (m : (Type u -> Type v)) (l : (Type u)) [Monad m] [CompleteLattice l] [MAlgOrdered m l]
  (n : (Type u -> Type w)) (k : outParam (Type u)) [Monad n] [CompleteLattice k] [MAlgOrdered n k]
  [MonadLiftT m n]
  where
    [cl : LogicLiftT l k]
    μ_lift (x : m α) : MAlg.lift (liftM (n := n) x) f = liftM (n := Cont k) (MAlg.lift x) f


instance MAlgLiftTRefl [Monad m] [CompleteLattice l] [LawfulMonad m] [MAlgOrdered m l] :
  MAlgLiftT m l m l where
    μ_lift := by simp

instance MAlgLiftTTrans
  [Monad m] [CompleteLattice l] [LawfulMonad m] [MAlgOrdered m l]
  [Monad n] [CompleteLattice k] [LawfulMonad n] [MAlgOrdered n k] [MonadLiftT m n]
  [Monad p] [CompleteLattice q] [LawfulMonad p] [MAlgOrdered p q] [MonadLift n p]
  [inst': MAlgLiftT m l n k] [inst: MAlgLift n k p q] :
  MAlgLiftT m l p q where
    cl := by
      let cl := inst.cl
      let cl' := inst'.cl
      refine instLogicLiftTOfLogicLift
    μ_lift := by
      intros; simp [liftM, instMonadLiftTContOfLogicLiftT, instLogicLiftTOfLogicLift,instMonadLiftTOfMonadLift];
      erw [inst.μ_lift]; congr! 2; ext; apply inst'.μ_lift
