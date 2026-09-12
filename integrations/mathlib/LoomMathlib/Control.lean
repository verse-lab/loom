import Loom.Control.Cont
import Loom.Control.Writer
import Mathlib.Control.Monad.Cont

/-! Explicit bridges avoid introducing competing global typeclass instances. -/

namespace LoomMathlib

@[implicit_reducible]
def logMonoidOfMonoid (ω : Type u) [Monoid ω] : Loom.LogMonoid ω where
  empty := 1
  append := (· * ·)
  append_assoc := mul_assoc
  empty_append := one_mul
  append_empty := mul_one

def contToLoom {r : Type u} {m : Type u → Type v} {α : Type w}
    (c : ContT r m α) : Loom.ContT r m α := c.run

def contFromLoom {r : Type u} {m : Type u → Type v} {α : Type w}
    (c : Loom.ContT r m α) : ContT r m α := c.run

theorem cont_roundtrip (c : ContT r m α) : contFromLoom (contToLoom c) = c := rfl

theorem cont_pure (a : α) : contToLoom (pure a : ContT r m α) = pure a := rfl

theorem cont_bind (c : ContT r m α) (f : α → ContT r m β) :
    contToLoom (c >>= f) = contToLoom c >>= (contToLoom ∘ f) := rfl

def writerToLoom (c : WriterT ω m α) : Loom.WriterT ω m α := c.run
def writerFromLoom (c : Loom.WriterT ω m α) : WriterT ω m α := c.run

theorem writer_roundtrip (c : WriterT ω m α) : writerFromLoom (writerToLoom c) = c := rfl

theorem writer_pure [Monad m] [Monoid ω] (a : α) :
    letI := logMonoidOfMonoid ω
    writerToLoom (pure a : WriterT ω m α) = pure a := rfl

theorem writer_bind [Monad m] [Monoid ω] (c : WriterT ω m α) (f : α → WriterT ω m β) :
    letI := logMonoidOfMonoid ω
    writerToLoom (c >>= f) = writerToLoom c >>= (writerToLoom ∘ f) := rfl

end LoomMathlib
