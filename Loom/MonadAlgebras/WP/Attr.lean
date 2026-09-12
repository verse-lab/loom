import Lean
import Loom.MonadAlgebras.WP.Liberal

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
    addImportedFn := fun a => a.foldl (fun s a => a.foldl (fun s (k, v) => s.insertKeyValue k v) s) DiscrTree.empty,
    addEntryFn    := fun s n => s.insertKeyValue n.1 n.2 ,
  }

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
    default
  else if let .str _ "_unary" := name then
    default
  else
    -- Normal execution
    x

initialize registerTraceClass `Loom (inherited := true)
register_simp_attr loomLogicSimp
