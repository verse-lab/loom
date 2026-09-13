import Loom.Order.Instances
import Loom.Control.Cont

/-! Instance search does not unfold the `Id` and `ContT` definitions by default.
These bridges expose their underlying order at each assumption level. -/

namespace Loom.Order

instance [h : LE α] : LE (Id α) := h
instance [h : Preorder α] : Preorder (Id α) := h
instance [h : PartialOrder α] : PartialOrder (Id α) := h
instance [LE α] [h : OrderTop α] : OrderTop (Id α) := h
instance [LE α] [h : OrderBot α] : OrderBot (Id α) := h
instance [h : Lattice α] : Lattice (Id α) := h
instance [h : CompleteLattice α] : CompleteLattice (Id α) := h
instance [h : BooleanAlgebra α] : BooleanAlgebra (Id α) := h
instance [h : CompleteBooleanAlgebra α] : CompleteBooleanAlgebra (Id α) := h

variable {r : Type u} {m : Type u → Type v} {α : Type w}

instance [LE (m r)] : LE (ContT r m α) :=
  show LE ((α → m r) → m r) from inferInstance
instance [Preorder (m r)] : Preorder (ContT r m α) :=
  show Preorder ((α → m r) → m r) from inferInstance
instance [PartialOrder (m r)] : PartialOrder (ContT r m α) :=
  show PartialOrder ((α → m r) → m r) from inferInstance
instance [LE (m r)] [OrderTop (m r)] : OrderTop (ContT r m α) :=
  show OrderTop ((α → m r) → m r) from inferInstance
instance [LE (m r)] [OrderBot (m r)] : OrderBot (ContT r m α) :=
  show OrderBot ((α → m r) → m r) from inferInstance
instance [Lattice (m r)] : Lattice (ContT r m α) :=
  show Lattice ((α → m r) → m r) from inferInstance
instance [CompleteLattice (m r)] : CompleteLattice (ContT r m α) :=
  show CompleteLattice ((α → m r) → m r) from inferInstance
instance [BooleanAlgebra (m r)] : BooleanAlgebra (ContT r m α) :=
  show BooleanAlgebra ((α → m r) → m r) from inferInstance
instance [CompleteBooleanAlgebra (m r)] : CompleteBooleanAlgebra (ContT r m α) :=
  show CompleteBooleanAlgebra ((α → m r) → m r) from inferInstance

end Loom.Order
