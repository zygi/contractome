import Lake
open Lake DSL

package bytecode {
  dependencies := #[
  {
    name := `assertCmd
    src := Source.git "https://github.com/pnwamk/lean4-assert-command" "main"
  }]
}
