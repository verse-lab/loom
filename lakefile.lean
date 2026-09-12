import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.32.0"

package Loom where
  leanOptions := #[⟨`pp.unicode.fun, true⟩] -- pretty-prints `fun a ↦ b`

@[default_target]
lean_lib Loom where
  globs := #[Glob.andSubmodules `Loom]

@[test_driver]
lean_lib LoomTest where
  globs := #[Glob.submodules `LoomTest]
