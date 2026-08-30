import Poincare.GlobalMove32ReentryFirstTransitionBreakpoint

namespace Poincare

/--
The recurrent polygonal loop reaches the shared-edge midpoint of the first
post-anchor Move32 site at the exact first-transition dyadic breakpoint.

This is only a specialization of the generic ordered-path evaluation theorem
to the exact ordered loop carried by the polygonal certificate.  It makes no
claim yet about freshness, filling labels, or cancellation.
-/
theorem witnessedReentryOrderedLoop_first_target_dyadic_probe
    {K : Triangulation}
    (crossing : WitnessedReentryCrossingCertificate K)
    (realized : ∀ n, (crossing.sites n).RealizedIn K)
    (steps : ∀ n, WitnessedReentryTransitionArc K
      (crossing.sites n) (crossing.sites (n + 1)) (realized n))
    (basepoint : triangulationTopologicalGeometricCarrier K)
    (hbase : basepoint =
      move32SharedEdgeMidpoint (crossing.sites crossing.anchorIndex)
        (realized crossing.anchorIndex)) :
    let m := crossing.predecessorIndex + 1 - crossing.anchorIndex
    ∃ u : unitInterval,
      (u : ℝ) = 1 / (2 : ℝ) ^ (m - 1) ∧
      witnessedReentryOrderedLoop
          crossing realized steps basepoint hbase u =
        move32SharedEdgeMidpoint
          (crossing.sites (crossing.anchorIndex + 1))
          (realized (crossing.anchorIndex + 1)) := by
  subst basepoint

  let q : Nat → triangulationTopologicalGeometricCarrier K := fun n =>
    move32SharedEdgeMidpoint (crossing.sites (crossing.anchorIndex + n))
      (realized (crossing.anchorIndex + n))

  let arcs : ∀ n, Path (q n) (q (n + 1)) := fun n => by
    let a := steps (crossing.anchorIndex + n)
    exact a.path.cast rfl (by apply Subtype.ext; rfl)

  let m := crossing.predecessorIndex + 1 - crossing.anchorIndex

  have hm : 0 < m := by
    dsimp [m]
    have hg := crossing.gap
    omega

  obtain ⟨u, hu, hpath⟩ :=
    orderedTransitionPath_first_target_dyadic_probe q arcs m hm

  refine ⟨u, hu, ?_⟩

  simpa [witnessedReentryOrderedLoop, q, arcs, m, Path.cast] using hpath

/-- Certificate-level first-transition breakpoint evaluation. -/
theorem WitnessedReentryPolygonalLoopCertificate.first_transition_dyadic_midpoint_probe
    {K : Triangulation}
    (c : WitnessedReentryPolygonalLoopCertificate K) :
    let m := c.crossing.predecessorIndex + 1 - c.crossing.anchorIndex
    ∃ u : unitInterval,
      (u : ℝ) = 1 / (2 : ℝ) ^ (m - 1) ∧
      c.polygonalLoop u =
        move32SharedEdgeMidpoint
          (c.crossing.sites (c.crossing.anchorIndex + 1))
          (c.realized (c.crossing.anchorIndex + 1)) := by
  rw [c.polygonalLoop_eq_ordered]
  exact
    witnessedReentryOrderedLoop_first_target_dyadic_probe
      c.crossing c.realized c.steps c.basepoint c.basepoint_eq

end Poincare
