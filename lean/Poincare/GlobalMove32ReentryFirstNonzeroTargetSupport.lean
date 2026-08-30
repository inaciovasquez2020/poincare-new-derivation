import Poincare.GlobalMove32ReentryPolygonalLoop

namespace Poincare

/-- The first positive point of the dyadically refined ordered recurrent loop
lies in the initial target tetrahedron of the anchor transition. -/
theorem witnessedReentryOrderedLoop_first_nonzero_initialTarget_supported_probe
    {K : Triangulation}
    (crossing : WitnessedReentryCrossingCertificate K)
    (realized : ∀ n, (crossing.sites n).RealizedIn K)
    (steps : ∀ n, WitnessedReentryTransitionArc K
      (crossing.sites n) (crossing.sites (n + 1)) (realized n))
    (basepoint : triangulationTopologicalGeometricCarrier K)
    (hbase : basepoint =
      move32SharedEdgeMidpoint (crossing.sites crossing.anchorIndex)
        (realized crossing.anchorIndex))
    (N : Nat) (hN : 0 < N) :
    let m := crossing.predecessorIndex + 1 - crossing.anchorIndex
    ∃ u : unitInterval,
      (u : ℝ) =
          1 / (((N * 2 ^ (m + 1) : Nat) : ℝ)) ∧
        ((witnessedReentryOrderedLoop
            crossing realized steps basepoint hbase u).1 ∈
          triangulationTopologicalTetBody
            (steps crossing.anchorIndex).initialTarget) := by
  classical
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
    have hgap := crossing.gap
    omega

  have hfirst :
      ∀ u : unitInterval,
        (u : ℝ) ≤ 1 / 4 →
        ((arcs 0 u).1 ∈
          triangulationTopologicalTetBody
            (steps crossing.anchorIndex).initialTarget) := by
    intro u hu
    dsimp [arcs]
    simpa using
      (steps crossing.anchorIndex).initial_quarter_supported u hu

  obtain ⟨u, hu, hsupport⟩ :=
    orderedTransitionPath_first_nonzero_refinement_supported_probe
      q arcs
      (fun y => y.1 ∈
        triangulationTopologicalTetBody
          (steps crossing.anchorIndex).initialTarget)
      hfirst N m hN hm

  refine ⟨u, hu, ?_⟩
  simpa [witnessedReentryOrderedLoop, q, arcs, m, Path.cast] using hsupport

/-- Certificate-level form of the first-positive-point target-support fact. -/
theorem WitnessedReentryPolygonalLoopCertificate.first_nonzero_initialTarget_supported_probe
    {K : Triangulation}
    (c : WitnessedReentryPolygonalLoopCertificate K)
    (N : Nat) (hN : 0 < N) :
    let m := c.crossing.predecessorIndex + 1 - c.crossing.anchorIndex
    ∃ u : unitInterval,
      (u : ℝ) =
          1 / (((N * 2 ^ (m + 1) : Nat) : ℝ)) ∧
        ((c.polygonalLoop u).1 ∈
          triangulationTopologicalTetBody
            (c.steps c.crossing.anchorIndex).initialTarget) := by
  rw [c.polygonalLoop_eq_ordered]
  exact
    witnessedReentryOrderedLoop_first_nonzero_initialTarget_supported_probe
      c.crossing c.realized c.steps c.basepoint c.basepoint_eq N hN

end Poincare
