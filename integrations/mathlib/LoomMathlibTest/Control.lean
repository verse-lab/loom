import LoomMathlib.Control

example (c : ContT r m α) (k : α → m r) :
    (LoomMathlib.contToLoom c).run k = c.run k := rfl

example (c : WriterT ω m α) : (LoomMathlib.writerToLoom c).run = c.run := rfl

-- Opting into a mathlib monoid does not change the direct list-log instance.
example : Loom.LogMonoid (List Nat) := inferInstance

example [Monoid ω] : Loom.LogMonoid ω := LoomMathlib.logMonoidOfMonoid ω
