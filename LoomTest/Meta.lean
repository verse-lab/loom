import Loom.Util.Meta

open Lean Elab Tactic

example : let x := 1; x = x := by
  run_tac
    let target ← Loom.Meta.getMainTarget
    unless target.isLet do throwError "target helper reduced a let binding"
  rfl

-- Model the long application whose source argument extraction rewrites.
private def subject : Expr :=
  mkAppN (mkConst `f) ((List.range 11).toArray.map mkNatLit)

#guard (Loom.Meta.setAppArg subject 10 (mkNatLit 42)).getAppArgs ==
  ((List.range 10).toArray.map mkNatLit).push (mkNatLit 42)
#guard (Loom.Meta.setAppArg subject 0 (mkNatLit 42)).getAppFn == mkConst `f
#guard Loom.Meta.setAppArg subject 11 (mkNatLit 42) == subject
