import Loom.Control.Cont
import Loom.Control.Writer

namespace LoomTest.Control

-- These tests deliberately import no Loom semantics or mathlib modules.
example : LawfulMonad (Loom.Cont Nat) := inferInstance
example : LawfulMonad (Loom.WriterT (List Nat) Option) := inferInstance

def contExample : Loom.Cont Nat Nat := do
  let x ← pure 3
  pure (x + 4)

#guard (contExample.run (· * 2)).run == 14

-- The result universe is independent of the answer universe.
example {α : Type u} (a : α) : Loom.Cont Bool α := pure a

def writerExample : Loom.Writer (List Nat) Nat := do
  Loom.WriterT.tell [1, 2]
  Loom.WriterT.tell [3]
  pure 7

#guard writerExample.run.run == (7, [1, 2, 3])

def writerFailure : Loom.WriterT (List Nat) Option Nat := do
  Loom.WriterT.tell [1]
  liftM (m := Option) (none : Option Nat)

#guard writerFailure.run == none

end LoomTest.Control

-- Standard operation laws are enough to construct a log model; no commutativity.
example {ω : Type u} (empty : ω) (append : ω → ω → ω)
    [Std.Associative append] [Std.LawfulIdentity append empty] : Loom.LogMonoid ω where
  empty := empty
  append := append
  toAssociative := inferInstance
  toLawfulIdentity := inferInstance

example {ω : Type u} [Loom.LogMonoid ω] :
    Std.Associative (Loom.LogMonoid.append (ω := ω)) := inferInstance
example {ω : Type u} [Loom.LogMonoid ω] :
    Std.LawfulIdentity (Loom.LogMonoid.append (ω := ω)) Loom.LogMonoid.empty := inferInstance
