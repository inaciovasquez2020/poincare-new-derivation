import Poincare.Triangulation

namespace Poincare

/--
External theorem axiom.

Status:
CONDITIONAL_EXTERNAL_THEOREM_ONLY.

Meaning:
This names the 3-dimensional Poincare theorem in the PL category.
It is not a repository-internal theorem closure.
It does not discharge the repository's axioms, sorries, or placeholder move semantics.
-/
axiom Perelman_PL :
  ∀ K : Triangulation, S3 K

theorem conditional_PL_poincare_recognition
    (K : Triangulation) :
    S3 K :=
  Perelman_PL K

end Poincare
