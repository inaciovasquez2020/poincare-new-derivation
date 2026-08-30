import Poincare.GlobalMove32ReentryPolygonalLoop

namespace Poincare

/--
A strictly positive coordinate at the source of the ordered recurrent
polygonal loop must be one of the two endpoints of the anchor shared edge.

This is the exact support anchor needed to connect later finite boundary-cell
labels to the Move32 recurrence data.  It asserts no filling exit, descent, or
contradiction.
-/
theorem WitnessedReentryPolygonalLoopCertificate.source_positive_coordinate_eq_anchor_endpoint
    {K : Triangulation}
    (p : WitnessedReentryPolygonalLoopCertificate K)
    {v : Nat}
    (hv : 0 < (p.polygonalLoop (0 : unitInterval)).1 v) :
    v = (p.crossing.sites p.crossing.anchorIndex).d ∨
      v = (p.crossing.sites p.crossing.anchorIndex).e := by
  have hv' :
      0 <
        (move32SharedEdgeMidpoint
          (p.crossing.sites p.crossing.anchorIndex)
          (p.realized p.crossing.anchorIndex)).1 v := by
    rw [p.polygonalLoop.source, p.basepoint_eq] at hv
    exact hv

  rcases eq_or_ne v (p.crossing.sites p.crossing.anchorIndex).d with hvd | hvd
  · exact Or.inl hvd

  rcases eq_or_ne v (p.crossing.sites p.crossing.anchorIndex).e with hve | hve
  · exact Or.inr hve

  have hdv : (p.crossing.sites p.crossing.anchorIndex).d ≠ v :=
    Ne.symm hvd
  have hev : (p.crossing.sites p.crossing.anchorIndex).e ≠ v :=
    Ne.symm hve

  change
    0 <
      triangulationTopologicalGeometricEdgeMidpoint
        (p.crossing.sites p.crossing.anchorIndex).d
        (p.crossing.sites p.crossing.anchorIndex).e v at hv'

  simp [triangulationTopologicalGeometricEdgeMidpoint_apply, hdv, hev] at hv'

end Poincare
