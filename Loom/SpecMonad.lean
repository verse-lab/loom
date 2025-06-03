import Mathlib.Order.Basic

universe u v w

variable (m : Type u -> Type w) (w : Type u -> Type v)

class PreOrderFunctor where preord : (α : Type u) -> Preorder (w α)
instance [inst: (α : Type u) -> Preorder (w α)] : PreOrderFunctor w := ⟨inst⟩
instance (α : Type u) [inst: PreOrderFunctor w] : Preorder (w α) := inst.preord α

class MonadOrder extends Monad w, PreOrderFunctor w where
  bind_le {α : Type u} {β : Type u} (x y : w α) (f g : α -> w β) :
    x ≤ y → (∀ a, f a ≤ g a) → bind x f ≤ bind y g

class LawfulMonadLift (w : outParam (Type u -> Type v)) [Monad m] [Monad w] [MonadLiftT m w] where
  lift_pure {α : Type u} (x : α) : monadLift (pure (f := m) x) = pure (f := w) x
  lift_bind {α : Type u} {β : Type u} (x : m α) (f : α -> m β) : monadLift (bind (m := m) x f) = bind (m := w) (monadLift x) (fun x => monadLift (f x))

export LawfulMonadLift (lift_pure lift_bind)

class LawfulMonadLiftT (w : (Type u -> Type v)) [Monad m] [Monad w] [MonadLiftT m w] where
  lift_pure {α : Type u} (x : α) : monadLift (pure (f := m) x) = pure (f := w) x
  lift_bind {α : Type u} {β : Type u} (x : m α) (f : α -> m β) : monadLift (bind (m := m) x f) = bind (m := w) (monadLift x) (fun x => monadLift (f x))

lemma lift_map {α : Type u} {β : Type u} (f : α -> β) (x : m α)
  [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n] :
  liftM (f <$> x) = f <$> liftM (n := n) x := by
    rw [map_eq_pure_bind, liftM, LawfulMonadLiftT.lift_bind]
    simp [LawfulMonadLiftT.lift_pure]

instance [Monad m] : LawfulMonadLiftT m m where
  lift_pure := by simp [monadLift, lift_pure]
  lift_bind := by simp [monadLift, lift_bind]

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (StateT σ m) where
  lift_pure := by simp [monadLift, MonadLift.monadLift]; intros; ext; simp
  lift_bind := by simp [monadLift, MonadLift.monadLift]; intros; ext; simp

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (ReaderT σ m) where
  lift_pure := by simp [monadLift, MonadLift.monadLift]; intros; ext; simp [ReaderT.run, pure, ReaderT.pure]
  lift_bind := by simp [monadLift, MonadLift.monadLift]; intros; ext; simp [ReaderT.run, bind, ReaderT.bind]

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (ExceptT ε m) where
  lift_pure := by simp [monadLift, MonadLift.monadLift];
  lift_bind := by simp [monadLift, MonadLift.monadLift]; intros; ext; simp

instance [Monad m] [LawfulMonad m]
  [Monad n] [LawfulMonad n] [MonadLiftT m n] [inst: LawfulMonadLiftT m n]
  [Monad p] [LawfulMonad p] [MonadLift n p] [inst':LawfulMonadLift n p]
  : LawfulMonadLiftT m p where
    lift_pure := by simp [instMonadLiftTOfMonadLift, inst.lift_pure]; intros; apply inst'.lift_pure
    lift_bind := by simp [instMonadLiftTOfMonadLift, inst.lift_bind]; intros; apply inst'.lift_bind

alias EffectObservation := LawfulMonadLift

-- class abbrev SpecMonad (m : Type u -> Type w) (w : Type u -> Type v) [Monad m] :=
--   MonadOrder w, MonadLiftT m w, EffectObservation m w

/-
  Spec for myM :
    - (A + E -> State -> Prop) -> State -> Prop
    - (A -> State -> Prop) -> State -> Prop + θ_tot
    - (A -> State -> Prop) -> State -> Prop + θ_part

    (A -> L) -> L

-/
