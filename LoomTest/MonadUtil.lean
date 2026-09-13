import Loom.MonadUtil
import Loom.SpecMonad
import Loom.Control.Writer
import Loom.Control.Persistent

open scoped Loom.Order

namespace LoomTest.MonadUtil

-- The utilities retain preorder-only assumptions and independent universes.
example {t : Type v} [Loom.Order.Preorder t] : LawfulMonad (W t) := inferInstance
example {t : Type v} {α : Type u} [Loom.Order.Preorder t] (a : α) : W t α := pure a
example [Loom.Order.BooleanAlgebra t] (c : Loom.Cont t α) :
    c.inv.inv = c := Loom.Cont.inv_inv c
example [Loom.Order.BooleanAlgebra t] {c : Loom.Cont t α} (h : c.monotone) :
    c.inv.monotone := Loom.Cont.monotone_inv h

def both : W Prop Bool := ⟨fun p => p true ∧ p false,
  fun _ _ h hp => ⟨h true hp.1, h false hp.2⟩⟩

example (p : Bool → Prop) : both.wp.inv p = ¬(¬p true ∧ ¬p false) := rfl
example (f : Bool → W Prop Nat) (p : Nat → Prop) :
    (both >>= f).wp p = ((f true).wp p ∧ (f false).wp p) := rfl

def readLift : Loom.Cont (Nat → Prop) Nat :=
  liftM (m := Loom.Cont Prop) (fun p => p 7)

example (p : Nat → Nat → Prop) (s : Nat) : readLift p s = p 7 s := rfl
example : LawfulMonadLift (Loom.Cont Prop) (Loom.Cont (Nat → Prop)) := inferInstance

-- Ordered monad laws apply without requiring a lattice on its values.
def EqBox (α : Type u) := α

instance : Monad EqBox where
  pure := id
  bind x f := f x

instance : MonadOrder EqBox where
  toMonad := inferInstance
  preord _ := {
    le := Eq
    le_refl := fun _ => rfl
    le_trans := Eq.trans }
  bind_le := by
    intro α β x y f g h k
    cases h
    exact k x

example {α β : Type u} {x y : EqBox α} {f g : α → EqBox β}
    (h : x ⊑ₗ y) (k : ∀ a, f a ⊑ₗ g a) : (x >>= f) ⊑ₗ (y >>= g) :=
  MonadOrder.bind_le x y f g h k

-- Composed lawful lifts through a reader/state/exception stack.
abbrev Stack := ReaderT Bool (StateT Nat (ExceptT Unit Option))
example : LawfulMonadLiftT Option Stack := inferInstance
example (f : Nat → Bool) (x : Option Nat) :
    liftM (n := Stack) (f <$> x) = f <$> liftM (n := Stack) x := lift_map Option f x
example : EffectObservation Option (Loom.WriterT (List Nat) Option) := inferInstance

-- Persistent logs survive divergence, whereas WriterT stores logs with results.
def persistent : PeDivM (List Nat) Nat := do
  PeDivM.log [1, 2]
  PeDivM.log [3]
  pure 7

#guard persistent.1 == [1, 2, 3]
#guard (persistent.2.run : Nat) == 7

def diverging : PeDivM (List Nat) Nat := do
  PeDivM.log [1, 2]
  let _ ← (([], DivM.div) : PeDivM (List Nat) Unit)
  PeDivM.log [3]
  pure 7

#guard diverging.1 == [1, 2]
example : diverging.2 = DivM.div := rfl

def writerDiverging : Loom.WriterT (List Nat) DivM Nat := do
  Loom.WriterT.tell [1, 2]
  liftM (m := DivM) (DivM.div : DivM Unit)
  pure 7

example : writerDiverging.run = DivM.div := rfl
example [Loom.LogMonoid κ] : LawfulMonad (PeDivM κ) := inferInstance
example {κ : Type v} {α : Type u} [Loom.LogMonoid κ] (a : α) : PeDivM κ α := pure a
example [Monad m] [LawfulMonad m] [Loom.LogMonoid κ] :
    LawfulMonadLift m (Loom.WriterT κ m) := inferInstance

-- Explicit universe applications retain the original log-first order.
example : PeDivM.{0, 1} Unit Type := ((), .res Nat)
example : PeDivM.{1, 0} (List Type) Nat := ([Nat], .res 7)

section ExplicitPersistentUniverses
variable {κ : Type v} {α β : Type u} [Loom.LogMonoid κ]

example (k : κ) (a : α) : PeDivM.{v, u} κ α := (k, .res a)
example (k : κ) (x : PeDivM κ α) : PeDivM.prepend.{v, u} k x = x.prepend k := rfl
example (k : κ) (x : PeDivM κ α) : (x.prepend k).2 = x.2 :=
  PeDivM.prepend_snd_same.{v, u} k x
example (k k' : κ) (a : DivM α) :
    PeDivM.prepend k (k', a) = (Loom.LogMonoid.append k k', a) :=
  PeDivM.prepend.eq_1.{v, u} k k' a
example (x : PeDivM κ α) (f : α → PeDivM κ β) :
    (x >>= f).2 = x.2 >>= (Prod.snd ∘ f) := PeDivM.bind_snd.{v, u} x f
example (k : κ) : PeDivM κ PUnit.{u + 1} := PeDivM.log.{v, u} k

end ExplicitPersistentUniverses

end LoomTest.MonadUtil
