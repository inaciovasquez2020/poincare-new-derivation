import Poincare.GlobalMove32ReentryPolygonalLoop

namespace Poincare

/--
The ordered recurrent polygonal-loop certificate retains a witnessed reentry
step beginning at its anchor.  Hence the anchor Move32 source face is actually
represented in the triangulation.

This is only provenance recovery from the retained ordered transition.  It
asserts no Pachner exit, descent, or contradiction.
-/
theorem WitnessedReentryPolygonalLoopCertificate.anchor_sourceFace_obstruction
    {K : Triangulation}
    (p : WitnessedReentryPolygonalLoopCertificate K) :
    ∃ tau ∈ K.tets,
      (p.crossing.sites p.crossing.anchorIndex).a ∈ tau.verts ∧
      (p.crossing.sites p.crossing.anchorIndex).b ∈ tau.verts ∧
      (p.crossing.sites p.crossing.anchorIndex).c ∈ tau.verts := by
  have hgap :
      p.ordered.crossing.anchorIndex <
        p.ordered.crossing.predecessorIndex + 1 := by
    have hg := p.ordered.crossing.gap
    omega

  have hstep :=
    p.ordered.consecutive_witnessed
      p.ordered.crossing.anchorIndex
      (by omega)
      hgap

  rcases hstep with
    ⟨tau, rho, x, y, sigma,
      htau, _hrho, _hne,
      haTau, hbTau, hcTau, _⟩

  have haOrdered :
      (p.ordered.crossing.sites p.ordered.crossing.anchorIndex).a ∈
        tau.verts := by
    simpa only [p.ordered.traceAt_eq_site] using haTau

  have hbOrdered :
      (p.ordered.crossing.sites p.ordered.crossing.anchorIndex).b ∈
        tau.verts := by
    simpa only [p.ordered.traceAt_eq_site] using hbTau

  have hcOrdered :
      (p.ordered.crossing.sites p.ordered.crossing.anchorIndex).c ∈
        tau.verts := by
    simpa only [p.ordered.traceAt_eq_site] using hcTau

  refine ⟨tau, htau, ?_, ?_, ?_⟩
  · simpa [p.ordered_crossing] using haOrdered
  · simpa [p.ordered_crossing] using hbOrdered
  · simpa [p.ordered_crossing] using hcOrdered

end Poincare
