import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

package «tao-analysis-i» {
  -- add package configuration options here
}

lean_lib «TaoAnalysisI» {
  -- add library configuration options here
}

@[default_target]
lean_exe «tao-analysis-i» {
  root := `Main
}
