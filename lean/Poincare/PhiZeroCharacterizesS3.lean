import Poincare.Triangulation

namespace Poincare

theorem phi_zero_characterizes_s3 :
∀ T : Triangulation,
Phi T = 0 ↔ S3 T := by
intro T
simp [S3, normalized]

end Poincare
