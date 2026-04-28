import Lean
import Lean.Parser

open Lean Elab Command Term Meta Lean.Parser

inductive SmtSolver where
  | z3
  | cvc5
deriving BEq, Hashable, Inhabited

instance : ToString SmtSolver where
  toString
    | SmtSolver.z3  => "z3"
    | SmtSolver.cvc5 => "cvc5"

instance : Lean.KVMap.Value SmtSolver where
  toDataValue n := toString n
  ofDataValue?
  | "z3"  => some .z3
  | "cvc5" => some .cvc5
  | _     => none

/--
Options to control the solver used by the `loom_solve` tactic.
-/
inductive LoomSolver : Type where
  | cvc5
  | smt (smtSolver : SmtSolver)
  | grind
  | custom

instance : ToString LoomSolver where
  toString
    | .cvc5 => "cvc5"
    | .smt .z3 => "z3"
    | .smt .cvc5 => "cvc5"
    | .grind => "grind"
    | .custom => "custom"

instance : KVMap.Value LoomSolver where
  toDataValue
    | .cvc5 => "cvc5"
    | .smt .z3 => "z3"
    | .smt .cvc5 => "cvc5"
    | .grind => "grind"
    | .custom => "custom"
  ofDataValue?
    | .ofString s =>
      match s with
      | "grind" => some .grind
      | "z3" => some (.smt .z3)
      | "cvc5" => some (.smt .cvc5)
      | "custom" => some .custom
      | _ => none
    | _ => none

instance : Inhabited LoomSolver := ⟨.grind⟩

register_option loom.solver : LoomSolver := {
  defValue := .grind
  descr :=
  "Loom solver options. Right now we support
   - `cvc5` and `z3` to use the SMT solvers via `auto` tactic
   - `grind` to use the grind tactic
   - `custom` to use a user-provided solver tactic

  In the latter case, use has to provide a `solver_tactic` manually via
  ```lean
  macro_rules
  | `(tactic|loom_solver) => `(tactic|<solve_tactic>)
  ```
  "
}

register_option loom.solver.smt.default : SmtSolver := {
  defValue := .cvc5
  descr := "Default SMT solver to use if not specified explicitly via `loom.solver`. Default is `cvc5`."
}

register_option loom.solver.smt.retryOnUnknown : Bool := {
  defValue := true
  descr := "Should the query be retried with a different SMT solver if it the first check returns `unknown`? (default: true)"
}

register_option loom.solver.smt.timeout : Nat := {
  defValue := 1
  descr := "Timeout for cvc5 and z3 SMT solvers in seconds. Default is 1 second."
}

register_option loom.solver.smt.seed : Nat := {
  defValue := 0
  descr := "Seed for cvc5 and z3 SMT solvers. Default is 0."
}

register_option loom.solver.grind.splits : Nat := {
  defValue := 20
  descr := "Number of splits for grind tactic. Default is 20."
}

/--
Options to control the termination semantics of the proof.
-/
inductive LoomSemanticsTermination : Type where
  | part
  | total
  | unspecified

instance : Inhabited LoomSemanticsTermination := ⟨.unspecified⟩

instance : KVMap.Value LoomSemanticsTermination where
  toDataValue
    | .part => "partial"
    | .total => "total"
    | .unspecified => "unspecified"
  ofDataValue?
    | .ofString s =>
      match s with
      | "partial" => some .part
      | "total" => some .total
      | "unspecified" => some .unspecified
      | _ => none
    | _ => none

register_option loom.semantics.termination : LoomSemanticsTermination := {
  defValue := LoomSemanticsTermination.unspecified
  descr := "`(partial/total)` Option to control whether to check termination of methods using the `decreasing` annotations. Default is false."
}

/-
Options to control the non-deterministic choice semantics of the proof.
-/
inductive LoomSemanticsChoice : Type where
  | angelic
  | demonic
  | unspecified

instance : Inhabited LoomSemanticsChoice := ⟨.unspecified⟩

instance : KVMap.Value LoomSemanticsChoice where
  toDataValue
    | .angelic => "angelic"
    | .demonic => "demonic"
    | .unspecified => "unspecified"
  ofDataValue?
    | .ofString s =>
      match s with
      | "angelic" => some .angelic
      | "demonic" => some .demonic
      | "unspecified" => some .unspecified
      | _ => none
    | _ => none

register_option loom.semantics.choice : LoomSemanticsChoice := {
  defValue := .unspecified
  descr :=
  "Option to control the semantics of non-deterministic choice. Right now we support
  - `demonic` semantics. In this case, the specification of the method should be justified for all possible choices.
    Note that, in total correctness semantics, one also has to prove that all choices are feasible.
  - `angelic` semantics. In this case, the specification of the method should be justified for at least one choice.
  Default is `demonic` semantics.
  "
}

private def recordOption (stx : Syntax) : CommandElabM Unit := do
  let options ← Elab.elabSetOption stx[1] stx[3]
  modify fun s => { s with maxRecDepth := maxRecDepth.get options }
  modifyScope fun scope => { scope with opts := options }

private def openScope (ident : Name) : CommandElabM Unit := do
  let openDecls ← elabOpenDecl <| <- `(openDecl|$(mkIdent ident):ident)
  modifyScope fun scope => { scope with openDecls := openDecls }

/-
Normally, `set_option` commands are only recording options.
However, in Loom, we want our semantics control options to also open the corresponding scopes.
Maybe here we should define a custom `set_option` command, rather than mixing the Lean one.

Options for the solver will be used for each `prove_correct` command separately.
-/
elab_rules : command
  | `(command|set_option loom.semantics.termination $v) => do
    recordOption <| <- getRef
    match v with
    | `("partial") => openScope `PartialCorrectness
    | `("total") => openScope `TotalCorrectness
    | _ => throwError "invalid value for loom.semantics.termination"
  | `(command|set_option loom.semantics.choice $v) => do
    let opts <- getOptions
    /- Some times the non-deterministic choice semantics depends on the termination semantics.
      For example, in Velvet, in total correctness semantics, `x :| p x` has one more VC `∃ x, p x`.
      That means we need to determine the termination semantics first. -/
    if let "unspecified" := ( opts.get? `loom.semantics.termination ).getD "unspecified"  then
      throwError "First, you need to specify the termination semantics using `set_option loom.semantics.termination <partial/total>`"
    recordOption <| <- getRef
    match v with
    | `("angelic") => openScope <| `AngelicChoice
    | `("demonic") => openScope <| `DemonicChoice
    | _ => throwError "invalid value for loom.semantics.choice"


register_option loom.linter.warnings : Bool := {
  defValue := true
  descr := "`(true/false)` Option to control whether to show warnings related to Loom programms annotations."
}

register_option loom.linter.errors : Bool := {
  defValue := true
  descr := "`(true/false)` Option to control whether to show errors related to Loom programms annotations."
}


initialize
  registerTraceClass `loom.smt.debug
  registerTraceClass `loom.smt.result
  registerTraceClass `loom.smt.query
