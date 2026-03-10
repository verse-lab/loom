import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Control.Monad.Cont

universe u v w

-- Bridge instances so that type class resolution sees through `id` in `Cont`
-- and through the `def ContT` wrapper.
section ContInstances
variable {t : Type v}
instance instLEIdOfLE [inst : LE t] : LE (id t) := inst
instance instPreorderIdOfPreorder [inst : Preorder t] : Preorder (id t) := inst
instance instPartialOrderIdOfPartialOrder [inst : PartialOrder t] : PartialOrder (id t) := inst
instance instComplIdOfCompl [inst : Compl t] : Compl (id t) := inst
instance instBooleanAlgebraIdOfBooleanAlgebra [inst : BooleanAlgebra t] : BooleanAlgebra (id t) := inst
instance instCompleteLatticeIdOfCompleteLattice [inst : CompleteLattice t] : CompleteLattice (id t) := inst
instance instTopIdOfTop [inst : Top t] : Top (id t) := inst
instance instBotIdOfBot [inst : Bot t] : Bot (id t) := inst
end ContInstances

-- Bridge instances for ContT so instance search can find order/lattice instances
-- on `ContT r m α` (and hence on `Cont r α = ContT r id α`).
section ContTInstances
variable {r : Type u} {m : Type u → Type v} {α : Type w}
instance instLEContT [LE (m r)] : LE (ContT r m α) :=
  show LE ((α → m r) → m r) from inferInstance
instance instTopContT [Top (m r)] : Top (ContT r m α) :=
  show Top ((α → m r) → m r) from inferInstance
instance instBotContT [Bot (m r)] : Bot (ContT r m α) :=
  show Bot ((α → m r) → m r) from inferInstance
instance instPreorderContT [Preorder (m r)] : Preorder (ContT r m α) :=
  show Preorder ((α → m r) → m r) from inferInstance
instance instPartialOrderContT [PartialOrder (m r)] : PartialOrder (ContT r m α) :=
  show PartialOrder ((α → m r) → m r) from inferInstance
instance instCompleteLatticeContT [CompleteLattice (m r)] : CompleteLattice (ContT r m α) :=
  show CompleteLattice ((α → m r) → m r) from inferInstance
end ContTInstances

def Cont.inv {t : Type v} {α : Type u} [BooleanAlgebra t] (wp : Cont t α) : Cont t α :=
  fun f => (wp fun x => (f x)ᶜ)ᶜ

@[simp]
def Cont.monotone {t : Type v} {α : Type u} [Preorder t] (wp : Cont t α) :=
  ∀ (f f' : α -> t), (∀ a, f a ≤ f' a) → wp f ≤ wp f'

structure W (t : Type v) [Preorder t] (α : Type u) where
  wp : Cont t α
  wp_montone : wp.monotone

@[ext]
lemma W_ext (t : Type v) (α : Type u) [Preorder t] (w w' : W t α) :
  w.wp = w'.wp → w = w' := by intros; cases w; cases w'; simp_all

instance (t : Type v) [Preorder t] : Monad (W t) where
  pure x := ⟨fun f => f x, by solve_by_elim⟩
  bind x f := ⟨fun g => x.wp (fun a => (f a).wp g), by simp; intros; solve_by_elim [W.wp_montone]⟩

instance {l σ : Type u} : MonadLift (Cont l) (Cont (σ -> l)) where
  monadLift x := fun f s => x (f · s)



-- class Logic (t : Type u) extends SemilatticeInf t where
--   sat : t -> Prop
--   sat_monotone : ∀ {p₁ p₂ : t}, p₁ ≤ p₂ -> sat p₁ -> sat p₂
