import Poincare.Move32ClosedCorePreservation
import Poincare.Move32DegreeSupportBalance
import Poincare.Move32GeometricCarrierHomeomorph

namespace Poincare

/-- The exact local degree criterion for a legal `3-2` move packages into a
closed-core-preserving, topology-preserving strict `PhiSupport` descent. -/
theorem ClosedTriangulationCore.move32Site_replace_topologyPreserving_descent
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hlegal : s.LegalIn K)
    (hdegree :
      5 ≤ vertexDegree K s.d ∧
      5 ≤ vertexDegree K s.e ∧
      (6 ≤ vertexDegree K s.d ∨ 6 ≤ vertexDegree K s.e)) :
    ClosedTriangulationCore (s.replace K) ∧
      PhiSupport (s.replace K) < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier (s.replace K)) := by
  exact ⟨hcore.move32Site_replace_closedCore s hlegal,
    (hcore.move32Site_replace_PhiSupport_lt_iff s hlegal).2 hdegree,
    ⟨hcore.move32GeometricCarrierHomeomorph s hlegal⟩⟩

/-- Existential form of direct topology-preserving `3-2` descent. -/
theorem exists_closedCore_homeomorphic_PhiSupport_lt_of_move32
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hlegal : s.LegalIn K)
    (hdegree :
      5 ≤ vertexDegree K s.d ∧
      5 ≤ vertexDegree K s.e ∧
      (6 ≤ vertexDegree K s.d ∨ 6 ≤ vertexDegree K s.e)) :
    ∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K') := by
  exact ⟨s.replace K,
    hcore.move32Site_replace_topologyPreserving_descent s hlegal hdegree⟩

end Poincare
