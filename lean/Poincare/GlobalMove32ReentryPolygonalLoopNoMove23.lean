import Poincare.GlobalMove32ReentryPolygonalLoopFailClosed
import Poincare.GlobalMove32WitnessedReentryPerpetualNoMove23

namespace Poincare

/-- After absorbing the aligned legal-Move23 source-face branch into nonself
high-edge escape, an exact-three obstructed start produces the recurrence-driven
polygonal-loop certificate assuming only no strict descent and no nonself
high-edge escape. -/
theorem ClosedTriangulationCore.exists_polygonalLoopCertificate_of_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hSC : TriangulationRealizationSimplyConnected K)
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
    Nonempty (WitnessedReentryPolygonalLoopCertificate K) := by
  obtain ⟨sites, _hzero, hrealized, hthree, _hobstruction, hwitnessed⟩ :=
    hcore.exists_perpetual_witnessedReentry_of_noDescent_noHigh
      hlinks
      hconn
      hNoFour
      hNoDescent
      hNoHigh
      start
      hstartRealized
      hstartThree
      hstartObstruction

  obtain ⟨c, hsites⟩ :=
    hcore.exists_wholeCarrierLoop_of_witnessedReentry_recurrent_crossing_with_sites_eq
      hlinks
      hconn
      hSC
      hNoFour
      sites
      hrealized
      hthree
      hwitnessed

  have hrealizedC : ∀ n, (c.sites n).RealizedIn K := by
    intro n
    simpa [hsites] using hrealized n

  have hthreeC : ∀ n, (c.sites n).SharedEdgeExactlyThree K := by
    intro n
    simpa [hsites] using hthree n

  have hwitnessedC :
      ∀ n,
        Move32SourceFaceWitnessedReentry
          K (c.sites n) (c.sites (n + 1)) := by
    intro n
    simpa [hsites] using hwitnessed n

  exact
    hcore.exists_polygonalLoopCertificate_of_witnessedReentry_recurrent_crossing
      c
      hrealizedC
      hthreeC
      hwitnessedC

end Poincare
