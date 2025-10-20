import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice.Basic

universe u v w


/- Continuation monad definition -/
abbrev LoomCont (t : Type v) (α : Type u) := (α -> t) -> t

instance (t : Type v) : Monad (LoomCont t) where
  pure x := fun f => f x
  bind x f := fun g => x (fun a => f a g)

def LoomCont.inv {t : Type v} {α : Type u} [BooleanAlgebra t] (wp : LoomCont t α) : LoomCont t α :=
  fun f => (wp fun x => (f x)ᶜ)ᶜ

@[simp]
def LoomCont.monotone {t : Type v} {α : Type u} [Preorder t] (wp : LoomCont t α) :=
  ∀ (f f' : α -> t), (∀ a, f a ≤ f' a) → wp f ≤ wp f'

structure W (t : Type v) [Preorder t] (α : Type u) where
  wp : LoomCont t α
  wp_montone : wp.monotone

@[ext]
lemma W_ext (t : Type v) (α : Type u) [Preorder t] (w w' : W t α) :
  w.wp = w'.wp → w = w' := by intros; cases w; cases w'; simp_all

instance (t : Type v) [Preorder t] : Monad (W t) where
  pure x := ⟨fun f => f x, by solve_by_elim⟩
  bind x f := ⟨fun g => x.wp (fun a => (f a).wp g), by simp; intros; solve_by_elim [W.wp_montone]⟩

instance {l σ : Type u} : MonadLift (LoomCont l) (LoomCont (σ -> l)) where
  monadLift x := fun f s => x (f · s)



-- class Logic (t : Type u) extends SemilatticeInf t where
--   sat : t -> Prop
--   sat_monotone : ∀ {p₁ p₂ : t}, p₁ ≤ p₂ -> sat p₁ -> sat p₂
