import Lake
open Lake DSL

package «LeanOMIN» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LeanOMIN» where

lean_exe «leanomin» where
  root := `Main
