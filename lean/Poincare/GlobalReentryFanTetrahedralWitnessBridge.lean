import Poincare.GlobalFanReentryModeLinkedSuccessor

namespace Poincare

/-- The actual fail-closed reentry continuation retains the three tetrahedra
that witness transfer from the old source face to the reinjected high edge.
Unlike the unrestricted reentry_fan constructor, this existence theorem does
not permit an unrelated next fan.  The other alternative is an actual witnessed
reentry step.  Neither alternative asserts termination or strict descent. -/
theorem ClosedTriangulationCore.exists_reentry_fan_tetrahedral_witness_bridge
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hphi : 0 < PhiSupport K)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (old : WitnessedReentryState K) :
    (∃ s' : Move32Site,
      Move32SourceFaceWitnessedReentry K old.site s') ∨
    ∃ (next : HighFanState K) (tau rho sigma : Tet),
      tau ∈ K.tets ∧
      rho ∈ K.tets ∧
      sigma ∈ K.tets ∧
      ¬ SameTetVertices tau rho ∧
      old.site.a ∈ tau.verts ∧
      old.site.b ∈ tau.verts ∧
      old.site.c ∈ tau.verts ∧
      old.site.a ∈ rho.verts ∧
      old.site.b ∈ rho.verts ∧
      old.site.c ∈ rho.verts ∧
      next.v ∈ tau.verts ∧
      next.v ∉ [old.site.a, old.site.b, old.site.c] ∧
      next.x ∈ rho.verts ∧
      next.x ∉ [old.site.a, old.site.b, old.site.c] ∧
      next.v ∈ sigma.verts ∧
      next.x ∈ sigma.verts ∧
      FanReentryModeStep K (.reentry old) (.fan next) := by
  have hconnected : ConnectedLinkClosedCore K :=
    connectedLinkClosedCore_of_topologicalThreeManifold K hcore hM
  have hlinks :
      ∀ v ∈ vertexSupport K, VertexLinkConnected K v := hconnected.2
  have hconn : TetrahedronVertexOverlapConnected K :=
    hcore.tetrahedronVertexOverlapConnected_of_topologicalThreeManifold hM
  have hNoFour :
      ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4 := by
    rcases hcore.exists_topology_preserving_PhiSupport_descent_or_no_degree_four
        hlinks hconn hphi with hdesc | hno
    · exact (hNoDescent hdesc).elim
    · exact hno
  rcases
      hcore.exists_legal_move23_or_nonself_complementEdge_incidence_split_of_move32_sourceFace_obstruction
        hlinks hconn hNoFour old.site old.realized old.obstruction with
    ⟨m, _, _, _, hmlegal⟩ |
      ⟨tau, rho, p, q, sigma,
        htau, hrho, hne,
        haTau, hbTau, hcTau,
        haRho, hbRho, hcRho,
        hpTau, hpNot, hqRho, hqNot, hpq,
        hsigma, hpSigma, hqSigma, hnonself, hinc⟩
  · exact (hNoMove23 ⟨m, hmlegal⟩).elim
  rcases hinc with hthree | hhigh
  · rcases
        hcore.exists_descent_or_realized_sourceFace_obstruction_of_edgeIncidence_three
          hNoFour p q hpq hthree with
      hdesc | ⟨s', hsd, hse, hrealized', hthree', hobstruction'⟩
    · exact (hNoDescent hdesc).elim
    · exact Or.inl
        ⟨s', tau, rho, p, q, sigma,
          htau, hrho, hne,
          haTau, hbTau, hcTau,
          haRho, hbRho, hcRho,
          hpTau, hpNot, hqRho, hqNot, hpq,
          hsigma, hpSigma, hqSigma, hnonself,
          hsd, hse, hrealized', hthree', hobstruction'⟩
  · rcases
        hcore.exists_legal_move23_or_highFanState_on_edge_of_edgeIncidence_four_le
          hM hpq hsigma hpSigma hqSigma hhigh with
      hmove23 | ⟨next, hv, hx⟩
    · exact (hNoMove23 hmove23).elim
    · have hnextNonself :
          ¬ ((next.v = old.site.d ∧ next.x = old.site.e) ∨
             (next.v = old.site.e ∧ next.x = old.site.d)) := by
        simpa only [hv, hx] using hnonself
      refine Or.inr
        ⟨next, tau, rho, sigma,
          htau, hrho, hsigma, hne,
          haTau, hbTau, hcTau,
          haRho, hbRho, hcRho,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hv] using hpTau
      · simpa only [hv] using hpNot
      · simpa only [hx] using hqRho
      · simpa only [hx] using hqNot
      · simpa only [hv] using hpSigma
      · simpa only [hx] using hqSigma
      · exact FanReentryModeStep.reentry_fan old next hnextNonself

end Poincare
