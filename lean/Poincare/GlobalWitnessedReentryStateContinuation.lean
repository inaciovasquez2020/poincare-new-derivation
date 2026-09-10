import Poincare.GlobalFanChordContinuationReinjectHigh
import Poincare.GlobalMove32SourceFaceLegalMove23High

namespace Poincare

/-- Finite data needed to continue a witnessed source-face reentry branch. -/
structure WitnessedReentryState (K : Triangulation) where
  site : Move32Site
  realized : site.RealizedIn K
  three : site.SharedEdgeExactlyThree K
  obstruction :
    ∃ tau ∈ K.tets,
      site.a ∈ tau.verts ∧
      site.b ∈ tau.verts ∧
      site.c ∈ tau.verts

/-- Forget a witnessed reentry step to the continuation data carried by its
next exact-three Move32 site. -/
def witnessedReentryStateOfStep
    {K : Triangulation} {s s' : Move32Site}
    (h : Move32SourceFaceWitnessedReentry K s s') :
    WitnessedReentryState K := by
  have h' := h.toSourceFaceReentry
  exact
    {
      site := s'
      realized := h'.1
      three := h'.2.1
      obstruction := h'.2.2.1
    }

/-- Continue a witnessed-reentry state without assuming that high edges are
absent.  The aligned legal Move23 alternative has already been absorbed into
the high-edge branch; a high edge is then reinjected into an ambient fan.
Thus the only outputs are strict descent, another witnessed-reentry state, a
high-fan state, or a legal `2-3` move exposed while entering that new fan. -/
theorem ClosedTriangulationCore.WitnessedReentryState.continue_reinjectHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (r : WitnessedReentryState K) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    Nonempty (WitnessedReentryState K) ∨
    Nonempty (HighFanState K) := by
  rcases
      hcore.exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
        hlinks hconn hNoFour r.site r.realized r.obstruction with
    hdescent | hhigh | hreentry

  · exact Or.inr (Or.inl hdescent)

  · obtain ⟨p, q, sigma, hpq, hsigma, hp, hq, _hnonself, hinc⟩ := hhigh
    have hinc' :
        4 ≤ (K.tets.filter
          (fun gamma => p ∈ gamma.verts ∧ q ∈ gamma.verts)).length := by
      simpa using hinc

    rcases
        hcore.exists_legal_move23_or_highFanState_of_edgeIncidence_four_le
          hM hpq hsigma hp hq hinc' with
      hmove23 | hfan

    · exact Or.inl hmove23
    · exact Or.inr (Or.inr (Or.inr hfan))

  · obtain ⟨s', hstep⟩ := hreentry
    exact
      Or.inr
        (Or.inr
          (Or.inl
            ⟨witnessedReentryStateOfStep hstep⟩))

end Poincare
