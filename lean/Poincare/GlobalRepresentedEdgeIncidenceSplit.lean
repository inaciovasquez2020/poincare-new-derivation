import Poincare.GlobalRepresentedEdgeIncidenceLowerBound
import Mathlib.Tactic

namespace Poincare

/--
Every positively represented ambient edge of a closed triangulation has
either tetrahedron incidence exactly three or incidence at least four.
-/
theorem
    ClosedTriangulationCore.edgeIncidence_eq_three_or_four_le_of_pos
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hpos :
      0 <
        (K.tets.filter
          (fun tau =>
            v ∈ tau.verts ∧
            x ∈ tau.verts)).length) :
    (K.tets.filter
        (fun tau =>
          v ∈ tau.verts ∧
          x ∈ tau.verts)).length = 3 ∨
      4 ≤
        (K.tets.filter
          (fun tau =>
            v ∈ tau.verts ∧
            x ∈ tau.verts)).length := by
  have hthree :
      3 ≤
        (K.tets.filter
          (fun tau =>
            v ∈ tau.verts ∧
            x ∈ tau.verts)).length :=
    hcore.edgeIncidence_three_le_of_pos
      v x hvx hpos

  omega

end Poincare
