import Auto

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"

--method CubeSurfaceArea(size: int) returns (area: int)
--    requires size > 0
--    ensures area == 6 * size * size
--{
--    area := 6 * size * size;
--}

method CubeSurfaceArea (size: Int) return (area: Int)
    require size > 0
    ensures area = 6 * size * size
    do
    return 6 * size * size

prove_correct CubeSurfaceArea by
  loom_solve
