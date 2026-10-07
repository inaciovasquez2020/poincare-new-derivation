import Poincare.GlobalMove32PerpetualWitnessedReentryRecurrentCrossingNoMove23
import Poincare.GlobalMove32BothSourcesNoDegreeFour

namespace Poincare

set_option maxHeartbeats 800000 in

/--
The finite recurrent crossing produced by perpetual witnessed reentry already
contains both source tetrahedra of its predecessor Move32 site.

At the crossing, tau contains the predecessor source face and the returned d,
while rho contains the same source face and the returned e.  Since d and e
are the two distinct shared-edge endpoints, tau and rho are representatives
of sourceTet₀ and sourceTet₁.  The existing five-tetrahedron theorem therefore
forces degree four, contradicting the no-degree-four branch.
-/
theorem
    ClosedTriangulationCore.not_perpetual_witnessedReentry_of_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ x y sigma,
          x ≠ y ∧
          sigma ∈ K.tets ∧
          x ∈ sigma.verts ∧
          y ∈ sigma.verts ∧
          ¬ ((x = s.d ∧ y = s.e) ∨
             (x = s.e ∧ y = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (x ∈ gamma.verts ∧
                   y ∈ gamma.verts))).length)
    (start : Move32Site)
    (hstartRealized : start.RealizedIn K)
    (hstartThree : start.SharedEdgeExactlyThree K)
    (hstartObstruction :
      ∃ tau ∈ K.tets,
        start.a ∈ tau.verts ∧
        start.b ∈ tau.verts ∧
        start.c ∈ tau.verts) :
    False := by
  obtain ⟨sites, _hzero, hrealized, _hthree, _hobstruction, hwitnessed⟩ :=
    hcore.exists_perpetual_witnessedReentry_of_noDescent_noHigh
      hlinks hconn hNoFour hNoDescent hNoHigh
      start hstartRealized hstartThree hstartObstruction

  obtain ⟨i, k, tau, rho, _sigma, hconfig⟩ :=
    hcore.exists_finite_recurrent_return_crossing_configuration_of_perpetual_witnessedReentry
      sites hrealized _hthree hwitnessed

  rcases hconfig with
    ⟨_hgap, _hbound,
      htauK, hrhoK, _hsigmaK, hne,
      haTau, hbTau, hcTau,
      haRho, hbRho, hcRho,
      hdTau, heRho,
      _hdSigma, _heSigma,
      _heNotTau, _hdNotRho,
      _hsigmaTau, _hsigmaRho,
      hreturnEdge, _hsigmaTarget⟩

  have hs : Move32Site := sites k

  have hsource0 :
      ∃ t ∈ K.tets,
        SameTetVertices t hs.sourceTet₀ := by
    refine ⟨tau, htauK, ?_⟩
    intro z
    simp only [Move32Site.sourceTet₀, Tet.verts,
      List.mem_cons, List.mem_singleton] at *
    aesop

  have hsource1 :
      ∃ t ∈ K.tets,
        SameTetVertices t hs.sourceTet₁ := by
    refine ⟨rho, hrhoK, ?_⟩
    intro z
    simp only [Move32Site.sourceTet₁, Tet.verts,
      List.mem_cons, List.mem_singleton] at *
    aesop

  exact
    hcore.not_both_move32_sources_represented_of_no_degree_four
      hlinks hconn hNoFour hs (hrealized k) hsource0 hsource1

end Poincare
