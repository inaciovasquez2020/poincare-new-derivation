import Poincare.GlobalEdgeIncidenceThreeStarExtraction
import Poincare.VertexLinkMod2Chain
import Mathlib.Tactic

namespace Poincare

/--
An ambient edge of incidence three has three opposite-edge *occurrences*
among the triangles in its represented vertex-link star.

This counts incidences, not yet distinct perimeter edges. The separate
injectivity of opposite edges is required to promote it to a three-edge
boundary-set cardinality theorem.
-/
theorem ClosedTriangulationCore.three_star_perimeter_incidence_count
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hthree :
      (K.tets.filter
        (fun τ => v ∈ τ.verts ∧ x ∈ τ.verts)).length = 3) :
    ((vertexLinkStarTriangles K v x).attach.flatMap
      (fun σ =>
        (σ.1.edges
          (vertexLinkTriangles_triangle_nodup K hcore v σ.1
            ((mem_vertexLinkStarTriangles_iff K v x σ.1).1 σ.2).1)).filter
          (fun f => decide (¬(x = f.lo ∨ x = f.hi))))).length = 3 := by
  classical
  have hlen :
      (vertexLinkStarTriangles K v x).length = 3 :=
    hcore.vertexLinkStarTriangles_length_eq_three_of_edgeIncidence_three
      v x hvx hthree
  have hperimeter (σ : LinkTriangle) (hnodup : σ.verts.Nodup)
      (hx : x ∈ σ.verts) :
      ((σ.edges hnodup).filter
        (fun f => decide (¬(x = f.lo ∨ x = f.hi)))).length = 1 := by
    have hinc :
        ((σ.edges hnodup).filter
          (fun f => decide (x = f.lo ∨ x = f.hi))).length = 2 := by
      simpa [hx] using
        LinkTriangle.incident_edges_filter_length σ hnodup x
    have htotal :
        (σ.edges hnodup).length =
          ((σ.edges hnodup).filter
            (fun f => decide (x = f.lo ∨ x = f.hi))).length +
          ((σ.edges hnodup).filter
            (fun f => decide (¬(x = f.lo ∨ x = f.hi)))).length := by
      simpa only [decide_not] using
        (List.length_eq_length_filter_add
          (l := σ.edges hnodup)
          (fun f : LinkEdge => decide (x = f.lo ∨ x = f.hi)))
    have hlen : (σ.edges hnodup).length = 3 :=
      LinkTriangle.edges_length σ hnodup
    omega
  have hpoint
      (σ : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x}) :
      ((σ.1.edges
        (vertexLinkTriangles_triangle_nodup K hcore v σ.1
          ((mem_vertexLinkStarTriangles_iff K v x σ.1).1 σ.2).1)).filter
        (fun f => decide (¬(x = f.lo ∨ x = f.hi)))).length = 1 := by
    exact hperimeter σ.1
      (vertexLinkTriangles_triangle_nodup K hcore v σ.1
        ((mem_vertexLinkStarTriangles_iff K v x σ.1).1 σ.2).1)
      ((mem_vertexLinkStarTriangles_iff K v x σ.1).1 σ.2).2
  have hsum :
      ∀ l : List {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x},
        (l.map
          (fun σ =>
            ((σ.1.edges
              (vertexLinkTriangles_triangle_nodup K hcore v σ.1
                ((mem_vertexLinkStarTriangles_iff K v x σ.1).1 σ.2).1)).filter
              (fun f => decide (¬(x = f.lo ∨ x = f.hi)))).length)).sum =
          l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [hpoint a, ih]
        omega
  rw [List.length_flatMap]
  calc
    _ = (vertexLinkStarTriangles K v x).attach.length := hsum _
    _ = (vertexLinkStarTriangles K v x).length := by simp
    _ = 3 := hlen

end Poincare
