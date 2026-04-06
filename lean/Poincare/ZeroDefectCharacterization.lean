import Mathlib
import Poincare.ZeroDefect

namespace Poincare

theorem zero_defect_characterization_conditional' :
  ∀ T : Triangulation,
    Phi T = 0 →
    simply_connected T →
    S3 T := by
  intro T hPhi hpi1
  have hzero : ∀ v : Nat, delta T v = 0 := (Phi_zero_iff_local_zero T).mp hPhi
  have hsph : ∀ v : Nat, spherical_link T v := (local_zero_iff_spherical_links T).mp hzero
  exact global_s3_of_links_and_pi1 T hsph hpi1

end Poincare
