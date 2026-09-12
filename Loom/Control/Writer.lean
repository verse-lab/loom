import Loom.Control.Log
import Init.Control.Lawful
import Lean.Elab.Tactic.Ext

namespace Loom

universe u v

/-- A writer computation returns the result followed by the accumulated log. -/
def WriterT (ω : Type u) (m : Type u → Type v) (α : Type u) := m (α × ω)

abbrev Writer (ω : Type u) := WriterT ω Id

namespace WriterT

variable {ω α β : Type u} {m : Type u → Type v}

@[inline] def mk (x : m (α × ω)) : WriterT ω m α := x
@[inline] def run (x : WriterT ω m α) : m (α × ω) := x

@[simp] theorem run_mk (x : m (α × ω)) : (mk x).run = x := rfl
@[ext] theorem ext {x y : WriterT ω m α} (h : x.run = y.run) : x = y := h

instance [Monad m] [LogMonoid ω] : Monad (WriterT ω m) where
  pure a := mk (pure (a, LogMonoid.empty))
  map f x := mk ((fun (a, w) => (f a, w)) <$> x.run)
  bind x f := mk <| x.run >>= fun (a, w₁) =>
    (fun (b, w₂) => (b, LogMonoid.append w₁ w₂)) <$> (f a).run

variable [Monad m] [LogMonoid ω]

@[simp] theorem run_pure (a : α) :
    (pure a : WriterT ω m α).run = pure (a, LogMonoid.empty) := rfl
@[simp] theorem run_map (f : α → β) (x : WriterT ω m α) :
    (f <$> x).run = (fun (a, w) => (f a, w)) <$> x.run := rfl
@[simp] theorem run_bind (x : WriterT ω m α) (f : α → WriterT ω m β) :
    (x >>= f).run = x.run >>= fun (a, w₁) =>
      (fun (b, w₂) => (b, LogMonoid.append w₁ w₂)) <$> (f a).run := rfl

instance [LawfulMonad m] : LawfulMonad (WriterT ω m) := LawfulMonad.mk'
  (id_map := by intros; apply ext; simp)
  (pure_bind := by intros; apply ext; simp)
  (bind_assoc := by intros; apply ext; simp [LogMonoid.append_assoc])
  (bind_pure_comp := by intros; apply ext; simp)

instance : MonadLift m (WriterT ω m) where
  monadLift x := mk ((fun a => (a, LogMonoid.empty)) <$> x)

instance [LawfulMonad m] : LawfulMonadLift m (WriterT ω m) where
  monadLift_pure := by intros; apply ext; simp [MonadLift.monadLift]
  monadLift_bind := by intros; apply ext; simp [MonadLift.monadLift]

@[inline] def tell (w : ω) : WriterT ω m PUnit := mk (pure (⟨⟩, w))

omit [LogMonoid ω] in
@[simp] theorem run_tell (w : ω) : (tell (m := m) w).run = pure (⟨⟩, w) := rfl

end WriterT
end Loom
