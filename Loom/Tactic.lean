-- import Loom.MProp.HoareTriples
import Loom.Meta

open Lean Lean.Expr Lean.Meta
open Lean Elab Command Term Meta Tactic

open Tactic Lean.Meta

def anyGoalsWithTag (tactic : TacticM (Option (Name × α))) : TacticM (Array α) := do
  let mvarIds ← getGoals
  let mut res : Array α := #[]
  let mut mvarIdsNew : Array MVarId := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        let r ← tactic
        if let some ⟨n, r⟩ := r then
          let goals <- getUnsolvedGoals
          for goal in goals do
            goal.setTag n
          res := res.push r
          mvarIdsNew := mvarIdsNew ++ goals
      catch _ =>
        mvarIdsNew := mvarIdsNew.push mvarId
  setGoals mvarIdsNew.toList
  pure res

def anyGoals' (tactic : MVarId → TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut mvarIdsNew : Array MVarId := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tactic mvarId
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch _ =>
        mvarIdsNew := mvarIdsNew.push mvarId
  setGoals mvarIdsNew.toList
