import Mathlib.Order.Basic

universe u v w

variable (m : Type u -> Type w) (w : Type u -> Type v)

class PreOrderFunctor where preord : (α : Type u) -> Preorder (w α)
instance [inst: (α : Type u) -> Preorder (w α)] : PreOrderFunctor w := ⟨inst⟩
instance (α : Type u) [inst: PreOrderFunctor w] : Preorder (w α) := inst.preord α

class MonadOrder extends Monad w, PreOrderFunctor w where
  bind_le {α : Type u} {β : Type u} (x y : w α) (f g : α -> w β) :
    x ≤ y → (∀ a, f a ≤ g a) → bind x f ≤ bind y g

lemma lift_map {α : Type u} {β : Type u} (f : α -> β) (x : m α)
  [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n] :
  liftM (f <$> x) = f <$> liftM (n := n) x := by
    rw [map_eq_pure_bind, liftM, LawfulMonadLiftT.monadLift_bind]
    simp

instance [Monad m] : LawfulMonadLiftT m m where
  monadLift_pure := by simp [monadLift]
  monadLift_bind := by simp [monadLift]

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (StateT σ m) where
  monadLift_pure := by simp [monadLift, MonadLift.monadLift]; intros; ext; simp
  monadLift_bind := by simp [monadLift, MonadLift.monadLift]; intros; ext; simp

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (ReaderT σ m) where
  monadLift_pure := by simp [monadLift, MonadLift.monadLift]; intros; ext; simp [ReaderT.run, pure, ReaderT.pure]
  monadLift_bind := by simp [monadLift, MonadLift.monadLift]; intros; ext; simp [ReaderT.run, bind, ReaderT.bind]

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (ExceptT ε m) where
  monadLift_pure := by simp [monadLift, MonadLift.monadLift];
  monadLift_bind := by simp [monadLift, MonadLift.monadLift];

instance [Monad m] [LawfulMonad m]
  [Monad n] [LawfulMonad n] [MonadLiftT m n] [inst: LawfulMonadLiftT m n]
  [Monad p] [LawfulMonad p] [MonadLift n p] [inst':LawfulMonadLiftT n p]
  : LawfulMonadLiftT m p where
    monadLift_pure := by simp [instMonadLiftTOfMonadLift, inst.monadLift_pure]; intros; apply inst'.monadLift_pure
    monadLift_bind := by simp [instMonadLiftTOfMonadLift, inst.monadLift_bind]; intros; apply inst'.monadLift_bind

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
