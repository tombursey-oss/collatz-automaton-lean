import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.13.0"

package collatz_automaton

lean_lib CollatzAutomaton {
  srcDir := "src"
}

@[default_target]
lean_exe collatz_automaton {
  root := `Main
  srcDir := "src"
}
