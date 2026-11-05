import Poincare.VertexLinkSharedEndpointIntersection

open Set

namespace Poincare

/--
Finite-face realizations with disjoint vertex sets
have disjoint geometric realizations.
-/
theorem vertexLinkFiniteFaces_inter_eq_empty
    (s t : Finset Nat)
    (hdisjoint : s ∩ t = ∅) :
    convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑s : Set Nat)) ∩
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑t : Set Nat)) = ∅ := by
  calc
    convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑s : Set Nat)) ∩
        convexHull ℝ
          (triangulationTopologicalGeometricVertex ''
            (↑t : Set Nat)) =
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑(s ∩ t) : Set Nat)) :=
      vertexLinkFiniteFace_convexHull_inter_eq_commonVertices s t
    _ = ∅ := by
      simp [hdisjoint]

end Poincare
