/-
import Lean
import Auto
import Loom.MonadAlgebras.WP.Options

namespace Loom.SMT

/-- If the SMT solver returns `Unknown`, we try the other SMT solver. -/
def smtSolverToTryOnUnknown (tried : SmtSolver) : SmtSolver :=
  match tried with
  | .z3 => .cvc5
  | .cvc5 => .z3

abbrev SolverProc := IO.Process.Child ⟨.piped, .piped, .piped⟩

partial def Handle.readLineSkip (h : IO.FS.Handle) (skipLine : String := "\n") : IO String := do
  let rec loop := do
    let line ← h.getLine
    if line.isEmpty then
      return line
    if line == skipLine then
      loop
    else
      return line
  loop

inductive SmtResult
  /-- `modelString` contains the raw string returned by the solver. -/
  | Sat (modelString : Option String)
  | Unsat
  | Unknown (reason : Option String)
  | Failure (reason : Option String)
deriving Inhabited

instance : ToString SmtResult where
  toString
    | SmtResult.Sat none => "sat"
    | SmtResult.Sat (some m) => s!"sat\n{m}"
    | SmtResult.Unsat => s!"unsat"
    | SmtResult.Unknown none => s!"unknown"
    | SmtResult.Unknown (some r) => s!"unknown ({r})"
    | SmtResult.Failure none => "failure"
    | SmtResult.Failure (some r) => s!"failure ({r})"

/-- The directory of the file being currently compiled. -/
scoped syntax (name := currentDirectory) "currentDirectory!" : term

open Lean Elab Elab.Term in
@[term_elab currentDirectory] def elabCurrentFilePath : TermElab
  | `(currentDirectory!), _ => do
    let ctx ← readThe Lean.Core.Context
    let srcPath := System.FilePath.mk ctx.fileName
    let some srcDir := srcPath.parent
      | throwError "cannot compute parent directory of '{srcPath}'"
    return mkStrLit s!"{srcDir}"
  | _, _ => throwUnsupportedSyntax

open Lean Elab Tactic Meta Auto in
/-- Alternative to `prepareLeanSmtQuery`, this invokes `lean-auto` to generate the
  SMT query rather than `lean-smt`. The advantage is this is much faster
  (see
  [ufmg-smite#126](https://github.com/ufmg-smite/lean-smt/issues/126)),
  but produces unreadable queries. -/
def prepareLeanAutoQuery (mv : MVarId) (hints : TSyntax `Auto.hints) : TacticM String := do
  -- HACK: We operate on a cloned goal, and then reset it to the original.
  let goal := (← mkFreshExprMVar (← mv.getType)).mvarId!
  let (goalBinders, newGoal) ← goal.intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "prepareAutoQuery :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, inhFacts) ← collectAllLemmas hints #[] (goalBinders.push ngoal)
    let query ← getQueryFromAuto lemmas inhFacts
    -- IMPORTANT: Reset the goal to the original
    replaceMainGoal [mv]
    return query
  where
  -- based on `runAuto`
  getQueryFromAuto
    (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM String := do
    -- Simplify `ite`
    let ite_simp_lem ← Lemma.ofConst ``Auto.Bool.ite_simp (.leaf "hw Auto.Bool.ite_simp")
    let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem ite_simp_lem)
    -- Simplify `decide`
    let decide_simp_lem ← Lemma.ofConst ``Auto.Bool.decide_simp (.leaf "hw Auto.Bool.decide_simp")
    let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem decide_simp_lem)
    let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) (minds : Array (Array SimpleIndVal)) : LamReif.ReifM String := (do
      let exportFacts ← LamReif.reifFacts uvalids
      let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
      let _ ← LamReif.reifInhabitations uinhs
      let exportInds ← LamReif.reifMutInds minds
      LamReif.printValuation
      -- **Preprocessing in Verified Checker**
      let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
      exportFacts := exportFacts'
      getAutoQueryString exportFacts exportInds)
    let (cmdString, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM String) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (afterReify s.facts s.inhTys s.inds).run' {u := u})
    return cmdString
  getAutoQueryString (exportFacts : Array Embedding.Lam.REntry) (exportInds : Array Embedding.Lam.MutualIndInfo) : LamReif.ReifM String := do
    let lamVarTy := (← LamReif.getVarVal).map Prod.snd
    let lamEVarTy ← LamReif.getLamEVarTy
    let exportLamTerms ← exportFacts.mapM (fun re => do
      match re with
      | .valid [] t => return t
      | _ => throwError "runAuto :: Unexpected error")
    let sni : SMT.SMTNamingInfo :=
      {tyVal := (← LamReif.getTyVal), varVal := (← LamReif.getVarVal), lamEVarTy := (← LamReif.getLamEVarTy)}
    let ((commands, _validFacts), _state) ← (lamFOL2SMT sni lamVarTy lamEVarTy exportLamTerms exportInds).run
    trace[debug] "{_state.h2lMap.toArray}"
    let queryStr := String.intercalate "\n" (commands.toList.map toString)
    return queryStr

open Lean hiding Command Declaration

def emitCommandStr (p : SolverProc) (c : String) : MetaM Unit := do
  trace[loom.smt.query] "{c}"
  p.stdin.putStr c
  p.stdin.flush

def commandStr (c : Auto.IR.SMT.Command) : String := s!"{c}\n"

def emitCommand (p : SolverProc) (c : Auto.IR.SMT.Command) : MetaM Unit := do
  emitCommandStr p (commandStr c)

private def createAux (path : String) (args : Array String) : MetaM SolverProc := do
    trace[loom.smt.debug] "invoking {path} {args}"
    IO.Process.spawn {stdin := .piped, stdout := .piped, stderr := .piped,
                      cmd := path, args := args}

/-- FIXME: this is a hack to get the build directory; how to do this properly? -/
private def buildDir := System.mkFilePath [currentDirectory!] / ".." / ".lake" / "build"
def z3Path := buildDir / "z3"
def cvc5Path := buildDir / "cvc5"

def createSolver (name : SmtSolver) (withTimeout : Nat) : MetaM SolverProc := do
  let tlim_sec := withTimeout
  let seed := loom.solver.smt.seed.get $ ← getOptions
  match name with
  | .z3   => createAux s!"{z3Path}" #["-in", "-smt2", s!"-t:{tlim_sec * 1000}", s!"sat.random_seed={seed}", s!"smt.random_seed={seed}"]
  | .cvc5 =>
      let mut args := #["--lang", "smt", s!"--tlimit-per={tlim_sec * 1000}", "--seed", s!"{seed}"]
      let proc ← createAux s!"{cvc5Path}" args
      emitCommand proc (.setLogic "ALL")
      pure proc

def querySolver (goalQuery : String) (withTimeout : Nat) (forceSolver : Option SmtSolver := none) (retryOnUnknown : Bool := false) : MetaM (SmtResult × SmtSolver):= do
  let opts ← getOptions
  let solverName :=
    match forceSolver with
    | some s => s
    | none => loom.solver.smt.default.get opts
  try
  trace[loom.smt.debug] "solver: {solverName}"
  let solver ← createSolver solverName withTimeout
  emitCommandStr solver goalQuery
  emitCommand solver .checkSat
  let stdout ← solver.stdout.getLine
  trace[loom.smt.debug] "[checkSat] stdout: {stdout}"
  let (checkSatResponse, _) ← Auto.Solver.SMT.getTerm stdout
  match checkSatResponse with
  | .atom (.symb "sat") =>
    trace[loom.smt.result] "{solverName} says Sat"
    emitCommand solver .getModel
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    trace[loom.smt.debug] "stdout: {stdout}"
    trace[loom.smt.debug] "stderr: {stderr}"
    -- FIXME: why does this break after the update to v4.25.2?
    -- let (model, _) ← Auto.Solver.SMT.getTerm stdout
    solver.kill
    return (SmtResult.Sat .none, solverName)

  | .atom (.symb "unsat") =>
    trace[loom.smt.result] "{solverName} says Unsat"
    let (_, solver) ← solver.takeStdin
    let stdout ← solver.stdout.readToEnd
    let stderr ← solver.stderr.readToEnd
    trace[loom.smt.debug] "stdout: {stdout}"
    trace[loom.smt.debug] "stderr: {stderr}"
    solver.kill
    return (SmtResult.Unsat, solverName)

  | .atom (.symb "unknown") =>
    trace[loom.smt.result] "{solverName} says Unknown"
      if retryOnUnknown then
        let newSolver := smtSolverToTryOnUnknown solverName
        trace[loom.smt.debug] "Retrying with {newSolver}"
        querySolver goalQuery withTimeout (forceSolver := newSolver) (retryOnUnknown := false)
      else
        let (_, solver) ← solver.takeStdin
        let stdout ← solver.stdout.readToEnd
        let stderr ← solver.stderr.readToEnd
        trace[loom.smt.debug] "stdout: {stdout}"
        trace[loom.smt.debug] "stderr: {stderr}"
        solver.kill
        return (SmtResult.Unknown .none, solverName)

  | _ => throwError s!"Unexpected response from solver: {checkSatResponse}"
  catch e =>
    let exMsg ← e.toMessageData.toString
    return (.Failure s!"{exMsg}", solverName)
termination_by if retryOnUnknown then 1 else 0

-- /-- Our own version of the `auto` tactic. -/
syntax (name := loom_smt) "loom_smt" Auto.hints : tactic

open Lean Elab Tactic

/-- Axiom: We trust the SMT solver's judgment when it returns "unsat".
    When an SMT solver (Z3 or CVC5) determines that the negation of a goal
    is unsatisfiable, we accept the goal as proven. -/
axiom trust_smt : ∀ (p : Prop), p

private def solverStr (solver : Option SmtSolver := none) : String :=
  match solver with
  | some solver => s!"{solver}: "
  | none => ""

/-- A string to print when the solver returns `sat`. -/
def satGoalStr (solver : Option SmtSolver := none) : String := s!"{solverStr solver}the goal is false"
def unknownGoalStr (solver : Option SmtSolver := none) : String := s!"{solverStr solver}the goal is unknown"
def failureGoalStr (solver : Option SmtSolver := none) : String := s!"{solverStr solver}solver invocation failed"

def specifiedSmtSolver (loomSolver : LoomSolver) : Option SmtSolver :=
  match loomSolver with
  | .smt solver => some solver
  | _ => none

@[tactic loom_smt] def elabLoomSmt : Tactic := fun stx => withMainContext do
  let hints : TSyntax `Auto.hints := ⟨stx[1]⟩
  let mv ← Tactic.getMainGoal
  let opts ← getOptions
  let withTimeout := loom.solver.smt.timeout.get opts
  let cmdString ← prepareLeanAutoQuery mv hints
  let (res, solverUsed) ← querySolver cmdString withTimeout (forceSolver := specifiedSmtSolver (loom.solver.get opts)) (retryOnUnknown := loom.solver.smt.retryOnUnknown.get opts)
  match res with
  -- this shouldn't happen
  | .Sat none => throwError s!"{satGoalStr solverUsed}"
  | .Sat (some modelString) => throwError s!"{satGoalStr solverUsed}:{modelString}"
  | .Unknown reason => throwError "{unknownGoalStr solverUsed}{if reason.isSome then s!": {reason.get!}" else ""}"
  | .Failure reason => throwError "{failureGoalStr solverUsed}{if reason.isSome then s!": {reason.get!}" else ""}"
  | .Unsat =>
      -- Close the goal using our trust_smt axiom
      logInfo m!"Goal proven by {solverUsed}. Trusting SMT solver result."
      let goalType ← mv.getType
      let proof := mkApp (mkConst ``trust_smt) goalType
      mv.assign proof

end Loom.SMT
-/
