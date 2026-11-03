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


/-- Every legal 3-to-2 move on a closed core lowers PhiSupport by exactly four.
The no-degree-four and additional endpoint degree assumptions are unnecessary:
the replacement's closed core forces both endpoint degrees to be at least six
before the move. -/
theorem ClosedTriangulationCore.move32Site_replace_PhiSupport_add_four_eq
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hlegal : s.LegalIn K) :
    PhiSupport (s.replace K) + 4 = PhiSupport K := by
  have hcore' := hcore.move32Site_replace_closedCore s hlegal
  have memDegree (J : Triangulation) (v : Nat) :
      v ∈ vertexSupport J ↔ 0 < vertexDegree J v := by
    rw [mem_vertexSupport_iff]
    change v ∈ allVerts J ↔ 0 < (allVerts J).count v
    simp
  have hpos := hcore.move32Site_replace_sharedEdge_vertexDegree_pos s hlegal
  have hdMin : 4 ≤ vertexDegree (s.replace K) s.d :=
    hcore'.vertexDegree_ge_four_of_mem_vertexSupport
      ((memDegree (s.replace K) s.d).2 hpos.1)
  have heMin : 4 ≤ vertexDegree (s.replace K) s.e :=
    hcore'.vertexDegree_ge_four_of_mem_vertexSupport
      ((memDegree (s.replace K) s.e).2 hpos.2)
  rcases hcore.move32Site_replace_vertexDegree_site s hlegal with
    ⟨_, _, _, hdDegree, heDegree⟩
  have hdSix : 6 ≤ vertexDegree K s.d := by omega
  have heSix : 6 ≤ vertexDegree K s.e := by omega
  have hdAfter :
      vertexDegree (s.replace K) s.d = vertexDegree K s.d - 2 := by omega
  have heAfter :
      vertexDegree (s.replace K) s.e = vertexDegree K s.e - 2 := by omega
  have hdCases := vertexDefect_sub_two_classification
    (vertexDegree K s.d) (by omega)
  have heCases := vertexDefect_sub_two_classification
    (vertexDegree K s.e) (by omega)
  have hbalance := hcore.move32Site_replace_PhiSupport_balance s hlegal
  simp only [vertexDefect, targetDegree, hdAfter, heAfter] at hbalance
  rcases hdCases with hd3 | hd4 | hd5 | hd6 <;>
    rcases heCases with he3 | he4 | he5 | he6 <;> omega

end Poincare
