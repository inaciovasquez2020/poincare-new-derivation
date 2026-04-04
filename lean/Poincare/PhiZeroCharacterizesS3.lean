import Mathlib
import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

axiom phi_zero_characterizes_s3 :
  ∀ T : Triangulation,
    Phi T = 0 ↔ S3 T

end Poincare
