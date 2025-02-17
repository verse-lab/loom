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

alias EffectObservation := LawfulMonadLift

class abbrev SpecMonad (m : Type u -> Type w) (w : Type u -> Type v) [Monad m] :=
  MonadOrder w, MonadLiftT m w, EffectObservation m w

/-
  Spec for myM :
    - (A + E -> State -> Prop) -> State -> Prop
    - (A -> State -> Prop) -> State -> Prop + θ_tot
    - (A -> State -> Prop) -> State -> Prop + θ_part

    (A -> L) -> L

-/
