import Lake
open Lake DSL

package poincare_new_derivation where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib Poincare where
  srcDir := "lean"
