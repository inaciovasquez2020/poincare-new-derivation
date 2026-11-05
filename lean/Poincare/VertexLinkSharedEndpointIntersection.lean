import Poincare.VertexLinkFiniteFaceIntersection

open Set

namespace Poincare

/--
Two finite-face realizations sharing exactly one
vertex intersect precisely at that represented vertex.
-/
theorem vertexLinkFiniteFaces_inter_eq_sharedVertex
    (s t : Finset Nat)
    (v : Nat)
    (hcommon : s ∩ t = {v}) :
    convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑s : Set Nat)) ∩
      convexHull ℝ
        (triangulationTopologicalGeometricVertex ''
          (↑t : Set Nat)) =
    {triangulationTopologicalGeometricVertex v} := by
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
    _ = {triangulationTopologicalGeometricVertex v} := by
      simp [hcommon]

end Poincare
