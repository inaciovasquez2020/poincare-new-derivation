import Mathlib
import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

axiom normalization_implies_combinatorial_S3 :
  ∀ K : Triangulation,
    normalized K → S3 K

end Poincare
