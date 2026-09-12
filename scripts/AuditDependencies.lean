import Lean
import Lean.Util.FoldConsts

/-!
Run after `lake build`:

    lake env lean --run scripts/AuditDependencies.lean /tmp/loom-audit

The inventory records immediate dependencies of compiled declarations, including
generated declarations and inferred instances. It does not inventory syntax,
tactics, attributes, or the transitive dependencies of each referenced constant.
-/

open Lean

unsafe def main (args : List String) : IO Unit := do
  let [output] := args
    | throw <| IO.userError "usage: AuditDependencies.lean OUTPUT_DIRECTORY"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Loom }] {}
  let origin (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => .anonymous
  let mut rows : Array String := #[]
  let mut mathlibRefs : NameSet := {}
  let mut declarations := 0
  for (name, info) in env.constants.toList do
    let own := origin name
    if `Loom |>.isPrefixOf own then
      declarations := declarations + 1
      let typeRefs := info.type.getUsedConstantsAsSet
      for dep in info.getUsedConstantsAsSet do
        let depModule := origin dep
        if !(`Loom |>.isPrefixOf depModule) then
          let location := if typeRefs.contains dep then "type" else "value"
          rows := rows.push s!"{own}\t{name}\t{depModule}\t{dep}\t{location}"
          if `Mathlib |>.isPrefixOf depModule then
            mathlibRefs := mathlibRefs.insert dep
  let dir : System.FilePath := output
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "declarations.tsv") <|
    "loom_module\tdeclaration\tdependency_module\tdependency\tlocation\n" ++
      String.intercalate "\n" (rows.qsort (· < ·)).toList ++ "\n"
  let modules := env.header.moduleNames.map toString |>.qsort (· < ·)
  IO.FS.writeFile (dir / "modules.txt") <| String.intercalate "\n" modules.toList ++ "\n"
  let count := env.header.moduleNames.filter (`Mathlib |>.isPrefixOf ·) |>.size
  IO.println s!"{declarations} Loom declarations; {count} imported Mathlib modules; {mathlibRefs.size} distinct Mathlib references"
