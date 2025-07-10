import Auto
import Lean
import Lean.Parser

import Loom.MonadAlgebras.WP.Attr
import Loom.MonadAlgebras.WP.Tactic
-- import Loom.MonadAlgebras.WP.DoNames'
import Loom.MonadAlgebras.WP.Gen
import Loom.Tactic

import CaseStudies.Extension

import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.OfRpcMethod

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

private def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimplePersistentEnvExtension.get [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

def getAssertionStx : TacticM (Option Term) := withMainContext do
  let goal <- getMainTarget
  let goalStx <- ppExpr goal
  let ⟨_, ss, ns⟩ <- loomAssertionsMap.get
  let .some withNameExpr := goal.find? (fun e => e.isAppOf ``WithName)
    | let .some typeWithNameExpr := goal.find? (fun e => e.isAppOf ``typeWithName)
        | throwError s!"Failed to parse an assertion without names: {goalStx}"
      let nname := typeWithNameExpr.getAppArgs[2]!
      let sname <- nname.getName
      let some id1 := ns[sname]?
        | throwError s!"typeWithName {sname} not registered: {typeWithNameExpr}"
      return some ss[id1]!
  match_expr withNameExpr with
  | WithName exp name =>
    let name <- name.getName
    let some id := ns[name]?
      | let .some typeWithNameExpr := exp.find? (fun e => e.isAppOf ``typeWithName)
          | throwError s!"Failed to prove assertion without names: {goalStx}"
        let nname := typeWithNameExpr.getAppArgs[2]!
        let sname <- nname.getName
        let some id1 := ns[sname]?
          | throwError s!"typeWithName {sname} not registered: {typeWithNameExpr}"
        return some ss[id1]!
    return some ss[id]!
  | _ => throwError s!"Failed to prove assertion which is not registered4: {goalStx}"
  --let ⟨maxId, ss, ns⟩ <- loomAssertionsMap.get

declare_syntax_cat loom_solve_tactic
syntax "loom_solve" : loom_solve_tactic
syntax "loom_solve?" : loom_solve_tactic
syntax "loom_solve!" : loom_solve_tactic
syntax loom_solve_tactic : tactic

syntax "loom_goals_intro" : tactic
syntax "loom_unfold" : tactic
syntax "loom_auto" : tactic
syntax "loom_solver" : tactic

elab_rules : tactic
  | `(tactic| loom_goals_intro) => withMainContext do
    let vlsIntro <- `(tactic| (
      repeat' loom_intro
      wpgen
      try simp only [loomWpSimp]
      try unfold spec
      try simp only [invariants]
      try simp only [WithName.mk']
      try simp only [WithName.erase]
      try simp only [typeWithName.erase]
      try simp only [List.foldr]
      try simp only [loomLogicSimp]
      try simp only [iSup_apply, iSup_Prop_eq, exists_and_left, exists_and_right,
                     iInf_apply, iInf_Prop_eq, forall_and_left, forall_and_right]
      repeat loom_intro
      repeat' (loom_split <;> (repeat loom_intro))))
    evalTactic vlsIntro

elab_rules : tactic
  | `(tactic| loom_unfold) => withMainContext do
    let vlsUnfold <- `(tacticSeq|
      all_goals try unfold WithName at *
      all_goals try unfold typeWithName at *
      all_goals try unfold MProdWithName)
    evalTactic vlsUnfold

elab_rules : tactic
  | `(tactic| loom_auto) => withMainContext do
    let ctx := (<- solverHints.get)
    let mut hints : Array (TSyntax ``Auto.hintelem) := #[]
    for c in ctx do
      hints := hints.push $ <- `(Auto.hintelem| $(mkIdent c):ident)
    hints := hints.push $ <- `(Auto.hintelem| *)
    let vlsAuto <- `(tactic| try (try simp only [loomAbstractionSimp] at *); auto [$hints,*])
    evalTactic vlsAuto

elab_rules : tactic
  | `(tactic| $vls:loom_solve_tactic) => withMainContext do
    let vlsTryThis <- `(tacticSeq|
        loom_goals_intro
        loom_unfold
        loom_solver)
    if let `(loom_solve_tactic| loom_solve?) := vls then
      Tactic.TryThis.addSuggestion (<-getRef) vlsTryThis
    else
      let vlsIntro ← `(tactic| loom_goals_intro)
      let vlsUnfold ← `(tactic| loom_unfold)
      let vlsSolve ← `(tactic| loom_solver)
      evalTactic vlsIntro
      let res <- anyGoalsWithTag fun _mvarId => do
        let stx_res <- getAssertionStx
        evalTactic vlsUnfold
        let mvarId <- getMainGoal
        evalTactic vlsSolve
        if (<- getUnsolvedGoals).length > 0 then
          match stx_res with
          | some stx =>
            return some (.mkSimple stx.raw.prettyPrint.pretty, (mvarId, some stx))
          | none =>
            return some (`unnamed, (mvarId, none))
        else return none
      let tryVlsSolve ← `(tactic| all_goals try loom_solver)
      let tryVlsUnfold ← `(tactic| all_goals try loom_unfold)
      evalTactic tryVlsSolve
      evalTactic tryVlsUnfold
      match vls with
      | `(loom_solve_tactic| loom_solve!) =>
        for (mvarId, stx_res) in res do
          match stx_res with
          | some stx => logErrorAt stx $ m!"Failed to prove assertion\n{mvarId}"
          | none => logError m!"Failed to prove nameless assertion\n{mvarId}"
      | _ => pure ()

elab "loom_solve?" : tactic => withMainContext do
  let ctx := (<- solverHints.get)
  let mut hints : Array (TSyntax ``Auto.hintelem) := #[]
  for c in ctx do
    hints := hints.push $ <- `(Auto.hintelem| $(mkIdent c):ident)
  -- hints := hints.push $ <- `(Auto.hintelem| *)
  let tac <- `(tactic| (
  intro
  try simp only [$(mkIdent `loomAbstractionSimp):ident] at *
  wpgen
  try simp only [$(mkIdent `loomWpSimp):ident]
  try simp only [$(mkIdent `WithName):ident]
  try simp only [$(mkIdent `typeWithName):ident]
  try unfold spec
  try simp only [$(mkIdent `invariants):ident]
  try simp only [$(mkIdent `WithName.mk'):ident]
  try simp only [$(mkIdent `WithName.erase):ident]
  try simp only [$(mkIdent `typeWithName.erase):ident]
  try simp only [$(mkIdent `List.foldr):ident]
  try simp only [$(mkIdent `loomLogicSimp):ident]
  try simp only [$(mkIdent `simpMAlg):ident]
  repeat' (apply $(mkIdent `And.intro) <;> (repeat loom_intro))
  any_goals auto [$hints,*]
  ))
  Tactic.TryThis.addSuggestion (<-getRef) tac
