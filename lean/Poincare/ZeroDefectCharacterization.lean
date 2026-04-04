import Mathlib
import Poincare.Triangulation
import Poincare.Moves
import Poincare.PhiZeroCharacterizesS3

namespace Poincare

theorem zero_defect_characterizes_s3 :
  ∀ T : Triangulation,
    Phi T = 0 ↔ S3 T :=
  phi_zero_characterizes_s3

end Poincare
