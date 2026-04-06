import Mathlib
import Poincare.Triangulation

namespace Poincare

axiom spherical_link : Triangulation → Nat → Prop
axiom simply_connected : Triangulation → Prop
axiom delta : Triangulation → Nat → Nat

axiom Phi_zero_iff_local_zero :
  ∀ T : Triangulation, Phi T = 0 ↔ ∀ v : Nat, delta T v = 0

axiom local_zero_iff_spherical_links :
  ∀ T : Triangulation, (∀ v : Nat, delta T v = 0) ↔ ∀ v : Nat, spherical_link T v

axiom global_s3_of_links_and_pi1 :
  ∀ T : Triangulation,
    (∀ v : Nat, spherical_link T v) →
    simply_connected T →
    S3 T

theorem zero_defect_characterization_conditional :
  ∀ T : Triangulation,
    Phi T = 0 →
    simply_connected T →
    S3 T := by
  intro T hPhi hpi1
  have hzero : ∀ v : Nat, delta T v = 0 := (Phi_zero_iff_local_zero T).mp hPhi
  have hsph : ∀ v : Nat, spherical_link T v := (local_zero_iff_spherical_links T).mp hzero
  exact global_s3_of_links_and_pi1 T hsph hpi1

end Poincare
