import Loom.Order.Defs
import Init.Control.Lawful

open scoped Loom.Order

universe u v w

variable (m : Type u -> Type w) (w : Type u -> Type v)

class PreOrderFunctor where preord : (α : Type u) -> Loom.Order.Preorder (w α)
instance [inst: (α : Type u) -> Loom.Order.Preorder (w α)] : PreOrderFunctor w := ⟨inst⟩
instance (α : Type u) [inst: PreOrderFunctor w] : Loom.Order.Preorder (w α) := inst.preord α

class MonadOrder extends Monad w, PreOrderFunctor w where
  bind_le {α : Type u} {β : Type u} (x y : w α) (f g : α -> w β) :
    x ⊑ₗ y → (∀ a, f a ⊑ₗ g a) → bind x f ⊑ₗ bind y g

theorem lift_map {α : Type u} {β : Type u} (f : α -> β) (x : m α)
  [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n] :
  liftM (f <$> x) = f <$> liftM (n := n) x := by
    simp

instance [Monad m] : LawfulMonadLiftT m m where
  monadLift_pure := by simp
  monadLift_bind := by simp

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (StateT σ m) where
  monadLift_pure := by simp
  monadLift_bind := by simp

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (ReaderT σ m) where
  monadLift_pure := by simp
  monadLift_bind := by simp

instance [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (ExceptT ε m) where
  monadLift_pure := by simp
  monadLift_bind := by simp

instance [Monad m] [LawfulMonad m]
  [Monad n] [LawfulMonad n] [MonadLiftT m n] [inst: LawfulMonadLiftT m n]
  [Monad p] [LawfulMonad p] [MonadLift n p] [inst':LawfulMonadLiftT n p]
  : LawfulMonadLiftT m p where
    monadLift_pure := by simp
    monadLift_bind := by simp

/-- A lawful observation of computations into another monad. -/
abbrev EffectObservation := LawfulMonadLift
