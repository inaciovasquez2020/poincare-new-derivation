import Poincare.GlobalMove32PerpetualWitnessedReentryRecurrentCrossing
import Poincare.GlobalMove32WitnessedReentryPerpetualNoMove23

namespace Poincare

/-- Once the aligned legal-Move23 source-face branch has been absorbed into
nonself high-edge escape, the finite recurrent witnessed-reentry crossing
configuration requires only exclusion of strict descent and nonself high-edge
escape. -/
theorem
    ClosedTriangulationCore.exists_finite_recurrent_return_crossing_configuration_of_noDescent_noHigh
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
    ∃ sites : Nat → Move32Site,
      sites 0 = start ∧
      ∃ i k tau rho sigma,
        i + 1 < k + 1 ∧
        k + 1 ≤ Fintype.card (SupportedEdgeState K) ∧
        tau ∈ K.tets ∧
        rho ∈ K.tets ∧
        sigma ∈ K.tets ∧
        ¬ SameTetVertices tau rho ∧
        (sites k).a ∈ tau.verts ∧
        (sites k).b ∈ tau.verts ∧
        (sites k).c ∈ tau.verts ∧
        (sites k).a ∈ rho.verts ∧
        (sites k).b ∈ rho.verts ∧
        (sites k).c ∈ rho.verts ∧
        (sites (k + 1)).d ∈ tau.verts ∧
        (sites (k + 1)).e ∈ rho.verts ∧
        (sites (k + 1)).d ∈ sigma.verts ∧
        (sites (k + 1)).e ∈ sigma.verts ∧
        (sites (k + 1)).e ∉ tau.verts ∧
        (sites (k + 1)).d ∉ rho.verts ∧
        ¬ SameTetVertices sigma tau ∧
        ¬ SameTetVertices sigma rho ∧
        (((sites (k + 1)).d = (sites i).d ∧
            (sites (k + 1)).e = (sites i).e) ∨
         ((sites (k + 1)).d = (sites i).e ∧
            (sites (k + 1)).e = (sites i).d)) ∧
        (SameTetVertices sigma (sites i).targetTet₀ ∨
         SameTetVertices sigma (sites i).targetTet₁ ∨
         SameTetVertices sigma (sites i).targetTet₂) := by
  obtain ⟨sites, hzero, hrealized, hthree, _hobstruction, hwitnessed⟩ :=
    hcore.exists_perpetual_witnessedReentry_of_noDescent_noHigh
      hlinks hconn hNoFour hNoDescent hNoHigh
      start hstartRealized hstartThree hstartObstruction

  obtain ⟨i, k, tau, rho, sigma, hconfig⟩ :=
    hcore.exists_finite_recurrent_return_crossing_configuration_of_perpetual_witnessedReentry
      sites hrealized hthree hwitnessed

  exact ⟨sites, hzero, i, k, tau, rho, sigma, hconfig⟩

end Poincare
