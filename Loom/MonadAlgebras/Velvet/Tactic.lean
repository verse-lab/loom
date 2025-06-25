import Auto
import Lean
import Lean.Parser

import Loom.MonadAlgebras.WP.Attr
import Loom.MonadAlgebras.WP.Tactic
-- import Loom.MonadAlgebras.WP.DoNames'
import Loom.MonadAlgebras.WP.Gen
import Loom.Tactic

import Loom.MonadAlgebras.Velvet.Extension

open Lean
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Meta

-- lemma simpMProp (α β : Type) (P : _ -> Prop) :
--   (∀ a : MProdWithNames α β n, P a) =
--   (∀ a b, P ⟨a, b⟩) := by
--   sorry

private def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

def getAssertionStx : TacticM Term := withMainContext do
  let goal <- getMainTarget
  let goalStx <- ppExpr goal
  let .some withNameExpr := goal.find? (fun e => e.isAppOf ``WithName)
    | throwError s!"Failed to prove assertion which is not registered1: {goalStx}"
  match_expr withNameExpr with
  | WithName _ name =>
    let name <- name.getName
    let ⟨_, ss, ns⟩ <- loomAssertionsMap.get
    let some id := ns[name]?
      | throwError s!"Failed to prove assertion which is not registered3: {goalStx}"
    return ss[id]!
  | _ => throwError s!"Failed to prove assertion which is not registered4: {goalStx}"
  --let ⟨maxId, ss, ns⟩ <- loomAssertionsMap.get

elab "velvet_solve" : tactic => withMainContext do
  let ctx := (<- solverHints.get)
  let mut hints : Array (TSyntax ``Auto.hintelem) := #[]
  for c in ctx do
    hints := hints.push $ <- `(Auto.hintelem| $(mkIdent c):ident)
  hints := hints.push $ <- `(Auto.hintelem| *)
  evalTactic $ <- `(tactic| (
  intro; wpgen;
  try simp only [loomWpSimp]
  try unfold spec
  try simp only [invariants]
  try simp only [WithName.mk']
  try simp only [WithName.erase]
  try simp only [List.foldr]
  try simp only [loomLogicSimp]
  repeat' (loom_split <;> (repeat loom_intro))))
  let res <- anyGoalsWithTag do
    let stx <- getAssertionStx
    evalTactic $ <- `(tactic| all_goals try unfold WithName at *)
    -- mvarId.setTag $ s!"{stx}".toName
    evalTactic $ <- `(tactic| (
        try (try simp only [loomAbstractionSimp] at *); auto [$hints,*]
      ))
    if (<- getUnsolvedGoals).length > 0 then
      return some (Name.mkSimple stx.raw.prettyPrint.pretty, stx)
    else return none
  for stx in res do
    logErrorAt stx $ m!"Failed to prove assertion " ++ MessageData.ofSyntax stx

elab "velvet_solve?" : tactic => withMainContext do
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
  try unfold spec
  try simp only [$(mkIdent `invariants):ident]
  try simp only [$(mkIdent `WithName.mk'):ident]
  try simp only [$(mkIdent `WithName.erase):ident]
  try simp only [$(mkIdent `List.foldr):ident]
  try simp only [$(mkIdent `loomLogicSimp):ident]
  try simp only [$(mkIdent `simpMProp):ident]
  repeat' (apply $(mkIdent `And.intro) <;> (repeat loom_intro))
  any_goals auto [$hints,*]
  ))
  Tactic.TryThis.addSuggestion (<-getRef) tac
