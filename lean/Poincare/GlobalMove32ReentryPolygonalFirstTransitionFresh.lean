import Poincare.GlobalMove32ReentryPolygonalFirstTransitionBreakpoint
import Poincare.GlobalMove32WitnessedReentryFreshEndpoints

namespace Poincare

/--
At the first-transition dyadic breakpoint of the recurrent polygonal loop,
every coordinate belonging to the anchor Move32 carrier is zero.

The proof uses only the exact breakpoint evaluation and the already-certified
freshness of the next witnessed-reentry shared edge.  No filling-label or
cancellation conclusion is asserted here.
-/
theorem WitnessedReentryPolygonalLoopCertificate.first_transition_dyadic_anchorCarrier_coordinates_zero_of_no_degree_four
    {K : Triangulation}
    (c : WitnessedReentryPolygonalLoopCertificate K)
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4) :
    let s := c.crossing.sites c.crossing.anchorIndex
    let t := c.crossing.sites (c.crossing.anchorIndex + 1)
    let m := c.crossing.predecessorIndex + 1 - c.crossing.anchorIndex
    ∃ u : unitInterval,
      (u : ℝ) = 1 / (2 : ℝ) ^ (m - 1) ∧
      c.polygonalLoop u =
        move32SharedEdgeMidpoint t
          (c.realized (c.crossing.anchorIndex + 1)) ∧
      ∀ z ∈ [s.a, s.b, s.c, s.d, s.e],
        (c.polygonalLoop u).1 z = 0 := by
  dsimp only

  let s : Move32Site :=
    c.crossing.sites c.crossing.anchorIndex
  let t : Move32Site :=
    c.crossing.sites (c.crossing.anchorIndex + 1)

  have hstepTrace :=
    c.ordered.consecutive_witnessed
      c.crossing.anchorIndex
      (by rw [c.ordered_crossing])
      (by
        rw [c.ordered_crossing]
        have hg := c.crossing.gap
        omega)

  have hstep : Move32SourceFaceWitnessedReentry K s t := by
    rw [c.ordered.traceAt_eq_site, c.ordered.traceAt_eq_site] at hstepTrace
    rw [c.ordered_crossing] at hstepTrace
    simpa [s, t] using hstepTrace

  have hsRealized : s.RealizedIn K := by
    simpa [s] using c.realized c.crossing.anchorIndex

  have hdisj :
      List.Disjoint [t.d, t.e] [s.a, s.b, s.c, s.d, s.e] :=
    hcore.witnessedReentry_next_sharedEdge_disjoint_previous_carrier_of_no_degree_four
      hlinks hNoFour s t hsRealized hstep

  obtain ⟨u, hu, hloop⟩ :=
    c.first_transition_dyadic_midpoint_probe

  refine ⟨u, hu, ?_, ?_⟩
  · simpa [t] using hloop
  · intro z hz

    have hzd : z ≠ t.d := by
      intro hEq
      have hmem : t.d ∈ [s.a, s.b, s.c, s.d, s.e] := by
        simpa [hEq] using hz
      exact (List.disjoint_left.mp hdisj t.d (by simp) hmem)

    have hze : z ≠ t.e := by
      intro hEq
      have hmem : t.e ∈ [s.a, s.b, s.c, s.d, s.e] := by
        simpa [hEq] using hz
      exact (List.disjoint_left.mp hdisj t.e (by simp) hmem)

    rw [hloop]
    change triangulationTopologicalGeometricEdgeMidpoint t.d t.e z = 0
    simp [triangulationTopologicalGeometricEdgeMidpoint_apply, hzd.symm, hze.symm]

end Poincare
