module

public import Loom.Order.Instances
public import Loom.Control.Cont

@[expose] public section

-- Instance search does not unfold `Id` and `ContT`.
namespace Loom.Order

instance [h : LE α] : LE (Id α) := h
instance [h : CompleteLattice α] : CompleteLattice (Id α) := h
instance [h : CompleteBooleanAlgebra α] : CompleteBooleanAlgebra (Id α) := h

variable {r : Type u} {m : Type u → Type v} {α : Type w}

instance [CompleteLattice (m r)] : CompleteLattice (ContT r m α) :=
  inferInstanceAs (CompleteLattice ((α → m r) → m r))
instance [CompleteBooleanAlgebra (m r)] : CompleteBooleanAlgebra (ContT r m α) :=
  inferInstanceAs (CompleteBooleanAlgebra ((α → m r) → m r))

end Loom.Order
