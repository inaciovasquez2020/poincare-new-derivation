import Poincare.Triangulation
import Poincare.ZeroDefectCoreGap

namespace Poincare

theorem phi_zero_characterizes_s3 :
∀ T : Triangulation,
Phi T = 0 ↔ S3 T := by
  intro T
  change Phi T = 0 ↔ normalized T
  calc
    Phi T = 0 ↔ PhiSupport T = 0 :=
      (phiSupport_zero_iff_phi_zero T).symm
    _ ↔ normalized T := by
      simp [normalized, phiSupport_zero_iff_phi_zero]

end Poincare
