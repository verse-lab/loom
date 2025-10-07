import Loom.MonadAlgebras.Instances.StateT
import Loom.MonadAlgebras.Instances.ExceptT
import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'
import Mathlib.Tactic
import Lean

import CaseStudies.Cashmere.Syntax_Cashmere

import Loom.MonadAlgebras.WP.Tactic

section

open ExceptionAsSuccess TotalCorrectness

/- theorem: if a program satisfies a triple with False postcondition,
   and its precondition is satisfied, then it threw an exception with some error message d -/
theorem false_imp_except (pre: Bal → Prop) (code: ExceptT String (StateT Bal DivM) Bal) :
  triple pre code ⊥ → ∀ s, pre s -> ∃ (d: String), code.run.run' s = DivM.res (Except.error d) := by
    simp [triple, wp_part_eq, StateT.wp_eq, DivM.wp_eq]
    intro tr s; specialize tr s; revert tr; simp
    simp [ExceptT.run, StateT.run, Functor.map]
    rcases (code s) with ((_|_)|_) <;> simp

end
