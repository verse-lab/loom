-- import LoL.MProp.HoareTriples
import LoL.Meta

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

open Tactic Lean.Meta


elab "simp_lift" m:ident : tactic => do
  let ns <- getCurrNamespace
  let MProp.pure := mkIdent `MProp.pure
  let MProp.μ_lift := mkIdent `MProp.μ_lift
  let MProp.μ_pure := mkIdent <| ns ++ `MProp.μ_pure
  let lift_bind := mkIdent `lift_bind
  let monadMap_if := mkIdent `monadMap_if
  let cmd <- `(#gen_spec $MProp.μ_pure for $MProp.pure (m := $m))
  liftCommandElabM (Lean.Elab.Command.elabCommand cmd)
  Lean.Elab.Tactic.evalTactic $ <- `(tactic| (
    unfold Function.comp; dsimp
    rw [$MProp.μ_lift:ident]; simp only [$MProp.μ_pure:ident];
    unfold liftM; simp only [$lift_bind:ident, $monadMap_if:ident]; simp only [monadLift]
    ))
