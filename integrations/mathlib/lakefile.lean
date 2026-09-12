import Lake
open Lake DSL

package LoomMathlib

require Loom from "../.."
require mathlib from git "https://github.com/leanprover-community/mathlib4" @
  "81a5d257c8e410db227a6665ed08f64fea08e997" -- v4.32.0

@[default_target]
lean_lib LoomMathlib where
  globs := #[Glob.andSubmodules `LoomMathlib]

@[test_driver]
lean_lib LoomMathlibTest where
  globs := #[Glob.submodules `LoomMathlibTest]
