import Mathlib
import Poincare.Triangulation
import Poincare.Recognition

namespace Poincare

axiom delta : Triangulation → Nat → Nat
axiom spherical_link : Triangulation → Nat → Prop
axiom simply_connected : Triangulation → Prop

theorem Phi_zero_iff_local_zero :
  ∀ T : Triangulation, Phi T = 0 ↔ ∀ v : Nat, delta T v = 0 := by

  sorry

theorem local_zero_iff_spherical_links :
  ∀ T : Triangulation, (∀ v : Nat, delta T v = 0) ↔ ∀ v : Nat, spherical_link T v := by

  sorry

theorem global_s3_of_links_and_pi1 :
  ∀ T : Triangulation,
    (∀ v : Nat, spherical_link T v) →
    simply_connected T →
    S3 T := by

  sorry

theorem zero_defect_characterization_conditional :
  ∀ T : Triangulation,
    Phi T = 0 →
    simply_connected T →
    S3 T := by
  intro T hPhi hpi
  have hδ : ∀ v : Nat, delta T v = 0 := (Phi_zero_iff_local_zero T).mp hPhi
  have hlink : ∀ v : Nat, spherical_link T v := (local_zero_iff_spherical_links T).mp hδ
  exact global_s3_of_links_and_pi1 T hlink hpi


axiom invariant : Triangulation → Nat
theorem invariant_zero_implies_pi1_trivial :
  ∀ T : Triangulation, invariant T = 0 → simply_connected T := by
  sorry

theorem zero_defect_characterization_unconditional
  (T : Triangulation)
  (hΦ : Phi T = 0)
  (hI : invariant T = 0) :
  S3 T := by
  have hδ : ∀ v : Nat, delta T v = 0 := (Phi_zero_iff_local_zero T).mp hΦ
  have hlink : ∀ v : Nat, spherical_link T v := (local_zero_iff_spherical_links T).mp hδ
  have hsc : simply_connected T := invariant_zero_implies_pi1_trivial T hI
  exact global_s3_of_links_and_pi1 T hlink hsc

end Poincare
