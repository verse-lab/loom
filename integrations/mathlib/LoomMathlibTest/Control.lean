import LoomMathlib.Control
import LoomMathlib.Order
import Loom.MonadUtil
import Loom.SpecMonad
import Loom.Control.Persistent

example (c : ContT r m α) (k : α → m r) :
    (LoomMathlib.contToLoom c).run k = c.run k := rfl

example (c : WriterT ω m α) : (LoomMathlib.writerToLoom c).run = c.run := rfl

-- Opting into a mathlib monoid does not change the direct list-log instance.
example : Loom.LogMonoid (List Nat) := inferInstance

example [Monoid ω] : Loom.LogMonoid ω := LoomMathlib.logMonoidOfMonoid ω

section GenericLog
variable [Monoid ω]
local instance : Loom.LogMonoid ω := LoomMathlib.logMonoidOfMonoid ω

example (a : α) : (pure a : PeDivM ω α) = (1, DivM.res a) := rfl
example (k : ω) (x : PeDivM ω α) : x.prepend k = (k * x.1, x.2) := rfl
example : LawfulMonad (PeDivM ω) := inferInstance
example [Monad m] [LawfulMonad m] :
    LawfulMonadLift m (Loom.WriterT ω m) := inferInstance
end GenericLog

section GenericContinuation
variable [CompleteBooleanAlgebra t]
local instance : Loom.Order.CompleteBooleanAlgebra t := LoomMathlib.completeBooleanAlgebraOfMathlib t

example (c : Cont t α) (p : α → t) :
    Loom.Cont.inv (LoomMathlib.contToLoom c) p =
      @Compl.compl t _ (c (fun a => @Compl.compl t _ (p a))) := rfl
end GenericContinuation

example : LawfulMonad (W Prop) := inferInstance
