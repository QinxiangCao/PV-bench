import Lake

open Lake DSL

package pvbench where

-- qcpLean points to the QCP checkout's Lean/ directory.
require qcp_demos_llm_examples from
  (run_io do
    let some root := get_config? qcpLean
      | throw <| IO.userError "Set the QCP Lean library path with lake -KqcpLean=/path/to/QCP/Lean <command>"
    return System.FilePath.mk root / "examples")

@[default_target]
lean_lib PVBench where
  roots := #[`Algorithms, `Codeforces, `Data_structures, `Engineering]
  globs := #[`Algorithms.+, `Codeforces.+, `Data_structures.+, `Engineering.+]
