import Lake
open Lake DSL System

package contractome {
  dependencies := #[{
    name := `bytecode
    src := Source.path (FilePath.mk "bytecode")
  },
  {
    name := `mathlib
    src := Source.git "https://github.com/leanprover-community/mathlib4" "master"
  },
  {
    name := `assertCmd
    src := Source.git "https://github.com/pnwamk/lean4-assert-command" "main"
  }]
}
