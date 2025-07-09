import Lean
import Loom.MonadAlgebras.WP.Gen

-- This file is based on
-- https://github.com/AeneasVerif/aeneas/blob/6ff714176180068bd3873af759d26a7053f4a795/backends/lean/Aeneas/Progress/Init.lean

open Lean Meta

/- Discrimination trees map expressions to values. When storing an expression
   in a discrimination tree, the expression is first converted to an array
   of `DiscrTree.Key`, which are the keys actually used by the discrimination
   trees. The conversion operation is monadic, however, and extensions require
   all the operations to be pure. For this reason, in the state extension, we
   store the keys from *after* the transformation (i.e., the `DiscrTreeKey`
   below). The transformation itself can be done elsewhere.
 -/
abbrev DiscrTreeKey := Array DiscrTree.Key

abbrev DiscrTreeExtension (α : Type) :=
  SimplePersistentEnvExtension (DiscrTreeKey × α) (DiscrTree α)

def mkDiscrTreeExtension [Inhabited α] [BEq α] (name : Name := by exact decl_name%) :
  IO (DiscrTreeExtension α) :=
  registerSimplePersistentEnvExtension {
    name          := name,
    addImportedFn := fun a => a.foldl (fun s a => a.foldl (fun s (k, v) => s.insertCore k v) s) DiscrTree.empty,
    addEntryFn    := fun s n => s.insertCore n.1 n.2 ,
  }

inductive Loom.SpecType where
  | triple
  | wpgen
deriving Inhabited, BEq, Repr

structure Loom.Spec where
  ty : Loom.SpecType
  name : Name
  prio : ℕ
deriving Inhabited, BEq, Repr

instance : Ord Loom.Spec where
  compare a b := if a.prio < b.prio then .lt else if a.prio > b.prio then .gt else .eq

structure SpecAttr where
  attr : AttributeImpl
  ext  : DiscrTreeExtension Loom.Spec
  deriving Inhabited

/-- For the attributes

    If we apply an attribute to a definition in a group of mutually recursive definitions
    (say, to `foo` in the group [`foo`, `bar`]), the attribute gets applied to `foo` but also to
    the recursive definition which encodes `foo` and `bar` (Lean encodes mutually recursive
    definitions in one recursive definition, e.g., `foo._mutual`, before deriving the individual
    definitions, e.g., `foo` and `bar`, from this one). This definition should be named `foo._mutual`
    or `bar._mutual`, and we generally want to ignore it.

    TODO: same problem happens if we use decreases clauses, etc.

    Below, we implement a small utility to do so.
  -/
def attrIgnoreAuxDef (name : Name) (default : AttrM α) (x : AttrM α) : AttrM α := do
  -- TODO: this is a hack
  if let .str _ "_mutual" := name then
--    trace[Utils] "Ignoring a mutually recursive definition: {name}"
    default
  else if let .str _ "_unary" := name then
--    trace[Utils] "Ignoring a unary def: {name}"
    default
  else
    -- Normal execution
    x

initialize registerTraceClass `Loom (inherited := true)
register_simp_attr loomLogicSimp
register_simp_attr loomWpSimp
register_simp_attr loomWpSplit
register_simp_attr loomAbstractionSimp
register_simp_attr loomLogicLiftSimp
register_simp_attr loomWPGenRewrite


def getSpecKey (ty : Expr) : MetaM (Expr × Loom.SpecType) := do
  let (_xs, _bis, body) ← forallMetaTelescope ty
  let x <- match_expr body with
  | triple _m _mInst _α _l _lInst _mPropInst _pre x _post => pure (x, .triple)
  | WPGen _m _mInst _α _l _lInst _mPropInst x => pure (x, .wpgen)
  | _ => throwError s!"not a triple: {body}"
  -- if x.1.getAppFn'.isConst then
  --   return x
  -- else
  --   throwError s!"not an application of a constant: {x.1}"
  return x

/- The persistent map from expressions to pspec theorems. -/
initialize specAttr : SpecAttr ← do
  let ext ← mkDiscrTreeExtension `specMap
  let attrImpl : AttributeImpl := {
    name := `spec
    descr := "Marks theorems to use with the `mspec` tactic"
    add := fun thName stx attrKind => do
      let prio <- Attribute.Builtin.getPrio stx
      -- TODO: use the attribute kind
      unless attrKind == AttributeKind.global do
        throwError "invalid attribute 'spec', must be global"
      -- Lookup the theorem
      let env ← getEnv
      -- Ignore some auxiliary definitions (see the comments for attrIgnoreMutRec)
      attrIgnoreAuxDef thName (pure ()) do
        trace[Loom] "Registering spec theorem for {thName}"
        let thDecl := env.constants.find! thName
        let (fKey, specType) ← MetaM.run' do
          let mut ty := thDecl.type
          trace[Loom] "Theorem: {ty}"
          -- Normalize to eliminate the let-bindings
--          ty ← zetaReduce ty
--          trace[Loom] "Theorem after normalization (to eliminate the let bindings): {ty}"
          let fExpr ← getSpecKey ty
          trace[Loom] "Registering spec theorem for expr: {fExpr.1}"
          -- Convert the function expression to a discrimination tree key
          let key <- DiscrTree.mkPath fExpr.1
          return (key, fExpr.2)
        let env := ext.addEntry env ⟨fKey, ⟨specType, thName, prio⟩⟩
        setEnv env
        trace[Loom] "Saved the environment"
  }
  registerBuiltinAttribute attrImpl
  pure { attr := attrImpl, ext := ext }



def SpecAttr.find? (s : SpecAttr) (e : Expr) : MetaM (Array Loom.Spec) := do
  (s.ext.getState (← getEnv)).getMatch e

def SpecAttr.getState (s : SpecAttr) : MetaM (DiscrTree Loom.Spec) := do
  return s.ext.getState (← getEnv)

abbrev SolverHints := Array Name

initialize solverHints : SimpleScopedEnvExtension Name SolverHints ←
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s' a => s'.push a
  }
private def _root_.Lean.SimpleScopedEnvExtension.modify
  (ext : SimpleScopedEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

syntax (name:= solverHint) "solverHint" : attr
initialize registerBuiltinAttribute {
  name := `solverHint
  descr := "This is the solver hint"
  add := fun declName _ _ => solverHints.modify (·.push declName)
}
