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
    rcases σ with ⟨a, b, c⟩
    have hn : (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by
      simpa [LinkTriangle.verts] using hnodup
    rcases hn with ⟨⟨hab, hac⟩, hbc⟩
    have hx_cases : x = a ∨ x = b ∨ x = c := by
      simpa [LinkTriangle.verts] using hx
    rcases hx_cases with hxa | hxb | hxc
    · subst x
      simp [LinkTriangle.edges, LinkEdge.incident_ofDistinct_iff, hab, hac, hbc]
    · subst x
      simp [LinkTriangle.edges, LinkEdge.incident_ofDistinct_iff, hab, hac, hbc]
    · subst x
      simp [LinkTriangle.edges, LinkEdge.incident_ofDistinct_iff, hab, hac, hbc]
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
        simp [hpoint a, ih]
  rw [List.length_flatMap]
  calc
    _ = (vertexLinkStarTriangles K v x).attach.length := hsum _
    _ = (vertexLinkStarTriangles K v x).length := by simp
    _ = 3 := hlen

end Poincare
