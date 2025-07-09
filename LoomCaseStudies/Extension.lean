
import Lean

open Lean Elab Command Term Meta Lean.Parser

abbrev LocMutVarsCtx := Array (Nat × Ident)

initialize localMutVarsCtx :
  SimpleScopedEnvExtension (Nat × Ident) LocMutVarsCtx <-
  registerSimpleScopedEnvExtension {
    initial := #[]
    addEntry := fun s id => s.push id
  }

abbrev GlobalMutVarsCtx := Std.HashMap Name LocMutVarsCtx

initialize globalMutVarsCtx :
  SimpleScopedEnvExtension (Name × LocMutVarsCtx) GlobalMutVarsCtx <-
  registerSimpleScopedEnvExtension {
    initial := ∅
    addEntry := fun s (n, ids) => s.insert n ids
  }

initialize
  registerTraceClass `Loom.debug

structure VelvetObligation where
  binderIdents : TSyntaxArray `Lean.Parser.Term.bracketedBinder
  ids : Array Ident
  retId : Ident
  ret : Term
  pre : Term
  post : Term
deriving Inhabited

abbrev VelvetObligations := Std.HashMap Name VelvetObligation

initialize velvetObligations :
  SimplePersistentEnvExtension (Name × VelvetObligation) VelvetObligations <-
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (n, o) => s.insert n o
    addImportedFn := fun as => Id.run do
      let mut res : VelvetObligations := ∅
      for a in as do
        res := res.union <| Std.HashMap.ofList a.toList
      return res
  }

/-- Storing slightly more information than `VelvetObligation`.  -/
structure VelvetTestingCtx extends VelvetObligation where
  newIds : Array Ident
  modBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
deriving Inhabited

abbrev VelvetTestingContextMap := Std.HashMap Name VelvetTestingCtx

initialize velvetTestingContextMap :
  SimplePersistentEnvExtension (Name × VelvetTestingCtx) VelvetTestingContextMap ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (n, o) => s.insert n o
    addImportedFn := fun as => Id.run do
      let mut res : VelvetTestingContextMap := ∅
      for a in as do
        res := res.union <| Std.HashMap.ofList a.toList
      return res
  }
