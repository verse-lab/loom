import Lake
open Lake DSL

package LoomMathlib

require Loom from "../.."
require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679" -- v4.35.0

@[default_target]
lean_lib LoomMathlib where
  globs := #[Glob.andSubmodules `LoomMathlib]

@[test_driver]
lean_lib LoomMathlibTest where
  globs := #[Glob.submodules `LoomMathlibTest]
