module

public import Init.Control.Lawful
meta import Lean.Elab.Tactic.Ext

@[expose] public section

namespace Loom

universe u v w

/-- Continuations with an underlying answer computation. The value universe
is independent of both the answer and the underlying computation universes. -/
def ContT (r : Type u) (m : Type u → Type v) (α : Type w) := (α → m r) → m r

abbrev Cont (r : Type u) (α : Type w) := ContT r Id α

namespace ContT

variable {r : Type u} {m : Type u → Type v} {α β : Type w}

@[inline] def mk (f : (α → m r) → m r) : ContT r m α := f
@[inline] def run (c : ContT r m α) : (α → m r) → m r := c

@[ext] theorem ext {x y : ContT r m α} (h : ∀ k, x.run k = y.run k) : x = y :=
  funext h

instance : Monad (ContT r m) where
  pure x k := k x
  bind x f k := x (fun a => f a k)

@[simp] theorem run_mk (f : (α → m r) → m r) (k : α → m r) : (mk f).run k = f k := rfl
@[simp] theorem run_pure (x : α) (k : α → m r) :
    (pure x : ContT r m α).run k = k x := rfl
@[simp] theorem run_bind (x : ContT r m α) (f : α → ContT r m β) (k : β → m r) :
    (x >>= f).run k = x.run (fun a => (f a).run k) := rfl
@[simp] theorem run_map (f : α → β) (x : ContT r m α) (k : β → m r) :
    (f <$> x).run k = x.run (k ∘ f) := rfl

instance : LawfulMonad (ContT r m) := LawfulMonad.mk'
  (id_map := by intros; rfl)
  (pure_bind := by intros; rfl)
  (bind_assoc := by intros; rfl)

instance [Monad m] : MonadLift m (ContT r m) where
  monadLift x k := x >>= k

instance [Monad m] [LawfulMonad m] : LawfulMonadLift m (ContT r m) where
  monadLift_pure := by intros; funext k; exact pure_bind ..
  monadLift_bind := by intros; funext k; exact bind_assoc ..

end ContT
end Loom
