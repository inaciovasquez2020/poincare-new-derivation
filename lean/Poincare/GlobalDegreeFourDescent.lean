import Poincare.GlobalDegreeFourMove41OrFiveTet
import Poincare.Move41OuterDegreeGap
import Poincare.Move41TopologyPreservingDescent
import Poincare.GlobalFiveTetPhiZero

namespace Poincare

/-- A supported degree-four vertex gives a strict topology-preserving
`PhiSupport` descent whenever the support defect is positive. -/
theorem ClosedTriangulationCore.exists_topology_preserving_PhiSupport_descent_of_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hphi : 0 < PhiSupport K)
    {v : Nat}
    (hv : v ∈ vertexSupport K)
    (hdegree : vertexDegree K v = 4) :
    ∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K') := by
  obtain ⟨s, _hcenter, hlegal | hfive⟩ :=
    hcore.exists_move41Site_legalIn_or_globalFiveTetCluster_of_vertexDegree_eq_four
      hlinks hconn v hdegree
  · exact exists_closedCore_homeomorphic_PhiSupport_lt_of_move41
      hcore s hlegal
      (hcore.move41Site_outer_vertexDegree_ge_six s hlegal)
  · obtain ⟨tau₀, tau₁, tau₂, tau₃, target,
        _htau₀K, _htau₀, _htau₁K, _htau₁,
        _htau₂K, _htau₂, _htau₃K, _htau₃,
        _htargetK, _htarget, _hnodup, hglobal⟩ := hfive
    exact (hcore.not_five_tet_cover_of_PhiSupport_pos hphi
      tau₀ tau₁ tau₂ tau₃ target hglobal).elim

/-- Positive support defect splits cleanly into a certified degree-four
descent or the global no-degree-four branch. -/
theorem ClosedTriangulationCore.exists_topology_preserving_PhiSupport_descent_or_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hphi : 0 < PhiSupport K) :
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4) := by
  classical
  by_cases hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4
  · exact Or.inr hNoFour
  · push_neg at hNoFour
    obtain ⟨v, hv, hdegree⟩ := hNoFour
    exact Or.inl
      (hcore.exists_topology_preserving_PhiSupport_descent_of_degree_four
        hlinks hconn hphi hv hdegree)

end Poincare
