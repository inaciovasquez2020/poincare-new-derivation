import Poincare.Validity
import Poincare.TriangulationTopologicalS3Transport

namespace Poincare

/-- A strict topology-preserving `PhiSupport` descent at every positive value
terminates at a normalized closed triangulation whose canonical carrier is
homeomorphic to the original carrier. -/
theorem exists_normalized_homeomorphic_triangulation_of_strict_descent
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hdescent :
      ∀ {J : Triangulation},
        ClosedTriangulationCore J →
        0 < PhiSupport J →
        ∃ J',
          ClosedTriangulationCore J' ∧
          PhiSupport J' < PhiSupport J ∧
          Nonempty
            (triangulationTopologicalGeometricCarrier J ≃ₜ
              triangulationTopologicalGeometricCarrier J')) :
    ∃ K',
      ClosedTriangulationCore K' ∧
      normalized K' ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K') := by
  have hnormalize :
      ∀ n : Nat,
        ∀ J : Triangulation,
          PhiSupport J = n →
          ClosedTriangulationCore J →
          ∃ J',
            ClosedTriangulationCore J' ∧
            normalized J' ∧
            Nonempty
              (triangulationTopologicalGeometricCarrier J ≃ₜ
                triangulationTopologicalGeometricCarrier J') := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro J hphiJ hcoreJ
        by_cases hzero : PhiSupport J = 0
        · refine ⟨J, hcoreJ, ?_, ?_⟩
          · exact hzero
          · exact ⟨Homeomorph.refl _⟩
        · have hpos : 0 < PhiSupport J := Nat.pos_of_ne_zero hzero
          obtain ⟨J1, hcore1, hlt, ⟨e1⟩⟩ := hdescent hcoreJ hpos
          have hltN : PhiSupport J1 < n := by
            rw [← hphiJ]
            exact hlt
          obtain ⟨J2, hcore2, hnorm2, ⟨e2⟩⟩ :=
            ih (PhiSupport J1) hltN J1 rfl hcore1
          exact ⟨J2, hcore2, hnorm2, ⟨e1.trans e2⟩⟩
  exact hnormalize (PhiSupport K) K rfl hcore

end Poincare
