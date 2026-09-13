import Loom.Order.Control

/-! Standalone continuation semantics. The assertion relation is Loom's own
preorder; Lean's computation-domain order remains separate. -/

open scoped Loom.Order

universe u v

namespace Loom.Cont

/-- Dualize a continuation using Boolean complement. Completeness is not needed. -/
def inv {t : Type v} {α : Type u} [Order.BooleanAlgebra t] (wp : Cont t α) : Cont t α :=
  fun f => Order.compl (wp fun x => Order.compl (f x))

@[simp] def monotone {t : Type v} {α : Type u} [Order.Preorder t] (wp : Cont t α) :=
  ∀ (f f' : α → t), (∀ a, f a ≤ f' a) → wp f ≤ wp f'

@[simp] theorem inv_inv {t : Type v} {α : Type u} [Order.BooleanAlgebra t]
    (wp : Cont t α) : inv (inv wp) = wp := by
  funext f
  simp only [inv, Order.compl_compl]

theorem monotone_inv {t : Type v} {α : Type u} [Order.BooleanAlgebra t]
    {wp : Cont t α} (h : wp.monotone) : (inv wp).monotone := by
  intro f g hfg
  exact Order.compl_antitone (h _ _ fun a => Order.compl_antitone (hfg a))

/-- Evaluate a predicate at the current environment before observing it. -/
instance readerLift {l : Type v} {σ : Type u} : MonadLift (Cont l) (Cont (σ → l)) where
  monadLift x := fun f s => x (f · s)

instance {l : Type v} {σ : Type u} : LawfulMonadLift (Cont l) (Cont (σ → l)) where
  monadLift_pure := by intros; rfl
  monadLift_bind := by intros; rfl

end Loom.Cont

/-- Monotone predicate transformers over a generic assertion preorder. -/
structure W (t : Type v) [Loom.Order.Preorder t] (α : Type u) where
  wp : Loom.Cont t α
  wp_montone : wp.monotone

@[ext] theorem W_ext (t : Type v) (α : Type u) [Loom.Order.Preorder t] (w w' : W t α) :
    w.wp = w'.wp → w = w' := by
  intro h
  cases w
  cases w'
  cases h
  rfl

instance (t : Type v) [Loom.Order.Preorder t] : Monad (W t) where
  pure x := ⟨fun f => f x, fun _ _ h => h x⟩
  bind x f := ⟨fun g => x.wp (fun a => (f a).wp g),
    fun _ _ h => x.wp_montone _ _ fun a => (f a).wp_montone _ _ h⟩

instance (t : Type v) [Loom.Order.Preorder t] : LawfulMonad (W t) := LawfulMonad.mk'
  (id_map := by intros; apply W_ext; rfl)
  (pure_bind := by intros; apply W_ext; rfl)
  (bind_assoc := by intros; apply W_ext; rfl)
