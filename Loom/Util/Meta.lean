module

public meta import Lean

public meta section

namespace Loom.Meta

open Lean Meta Elab Tactic

/-- Read the target without weak-head normalization. Reducing it here could
inline the source join points that extraction needs to keep shared. -/
def getMainTarget : TacticM Expr := do
  return (← Lean.Elab.Tactic.getMainTarget).cleanupAnnotations

/-- Replace a zero-based application argument, keeping the other arguments.
Out-of-bounds updates leave the expression unchanged. -/
def setAppArg (e : Expr) (i : Nat) (arg : Expr) : Expr :=
  if i < e.getAppNumArgs then
    mkAppN e.getAppFn (e.getAppArgs.set! i arg)
  else e

end Loom.Meta
