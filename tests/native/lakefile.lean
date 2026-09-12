import Lake
open Lake DSL

package LoomNativeTest
require Loom from "../.."

lean_lib Consumer

@[default_target]
lean_exe smoke where
  root := `Main
