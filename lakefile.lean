import Lake
open Lake DSL

package autograder where
  precompileModules := true

lean_lib AutograderTests where
  globs := #[.submodules `AutograderTests]

@[default_target]
lean_exe autograder where
  root := `Main
  supportInterpreter := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "8cc7ae9e6c622a3462dea5a6a7ee03c8976a8d93"