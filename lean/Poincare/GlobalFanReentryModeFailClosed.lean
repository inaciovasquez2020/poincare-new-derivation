import Poincare.GlobalFanChordEdgeProgress
import Poincare.GlobalMove32ReentrySourceEdgeClosure

namespace Poincare

theorem ClosedTriangulationCore.no_perpetual_fanReentryMode_of_noMove23_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
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
          s.a ∈ tau.verts ∧ s.b ∈ tau.verts ∧ s.c ∈ tau.verts) →
        ¬ ∃ p q sigma,
          p ≠ q ∧ sigma ∈ K.tets ∧ p ∈ sigma.verts ∧ q ∈ sigma.verts ∧
          ¬ ((p = s.d ∧ q = s.e) ∨ (p = s.e ∧ q = s.d)) ∧
          4 ≤ (K.tets.filter (fun gamma =>
            decide (p ∈ gamma.verts ∧ q ∈ gamma.verts))).length)
    (states : Nat → FanReentryModeState K) :
    False := by
  classical
  by_cases hReentry : ∃ n, ∃ r : WitnessedReentryState K,
      states n = .reentry r
  · obtain ⟨n, r, hr⟩ := hReentry
    have hfalse :=
      hcore.not_perpetual_witnessedReentry_of_noDescent_noHigh_sourceEdge
        hlinks hconn hNoFour hNoDescent hNoHigh
        r.site r.realized r.three r.obstruction
    exact hfalse
  · have h0 : ∃ f : HighFanState K, states 0 = .fan f := by
      cases hstate : states 0 with
      | fan f => exact ⟨f, hstate⟩
      | reentry r => exact False.elim (hReentry ⟨0, r, hstate⟩)
    obtain ⟨f, hf⟩ := h0
    have hfalse :=
      hcore.no_perpetual_highFanState_of_noMove23_noDescent_noHigh
        hM hlinks hNoFour hNoMove23 hNoDescent hNoHigh f
    exact hfalse

end Poincare