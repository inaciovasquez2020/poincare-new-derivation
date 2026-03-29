import Lake
open Lake DSL

package «poincare-new-derivation»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Poincare
