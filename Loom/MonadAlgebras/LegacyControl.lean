import Mathlib.Order.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Control.Monad.Cont

/-! Temporary support for algebra/WP modules that still use mathlib's
continuations. Delete this module when those consumers are ported. Standalone
clients import `Loom.MonadUtil` instead. No new code should depend on this file. -/

universe u v w

-- Bridge instances so that type class resolution sees through `id` in `Cont`
-- and through the `def ContT` wrapper.
section ContInstances
variable {t : Type v}
instance instLEIdOfLE [inst : LE t] : LE (Id t) := inst
instance instPreorderIdOfPreorder [inst : Preorder t] : Preorder (Id t) := inst
instance instPartialOrderIdOfPartialOrder [inst : PartialOrder t] : PartialOrder (Id t) := inst
instance instComplIdOfCompl [inst : Compl t] : Compl (Id t) := inst
instance instBooleanAlgebraIdOfBooleanAlgebra [inst : BooleanAlgebra t] : BooleanAlgebra (Id t) := inst
instance instCompleteLatticeIdOfCompleteLattice [inst : CompleteLattice t] : CompleteLattice (Id t) := inst
instance instTopIdOfTop [inst : Top t] : Top (Id t) := inst
instance instBotIdOfBot [inst : Bot t] : Bot (Id t) := inst
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

instance {l σ : Type u} : MonadLift (Cont l) (Cont (σ -> l)) where
  monadLift x := fun f s => x (f · s)