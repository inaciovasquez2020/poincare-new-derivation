import Poincare.VertexLinkMod2BoundaryTwoRank
import Mathlib.Tactic

namespace Poincare

/-- A link edge containing the star center does not occur in the mod-2
boundary of the full collection of triangles through that center.
The two-triangles-per-edge requirement is furnished by the existing
closed-surface certificate. This is a prerequisite for counting the three
outer boundary edges of an exactly-three-triangle star. -/
theorem vertexLinkMod2_star_boundary_zero_of_center_endpoint
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v e : Nat)
    (hSurf : VertexLinkConnectedClosedSurfaceCertificate K v)
    (f : VertexLinkMod2Edge K hcore v)
    (hef : e = f.1.lo ∨ e = f.1.hi) :
    vertexLinkMod2BoundaryTwo K hcore v
        (fun σ => if e ∈ σ.1.verts then (1 : ZMod 2) else 0) f = 0 := by
  classical
  have hfList : f.1 ∈ vertexLinkEdges K hcore v :=
    (List.mem_toFinset).1 f.2
  have hrep : f.1.RepresentedAt K v :=
    (mem_vertexLinkEdges_iff K hcore v f.1).1 hfList
  let T := VertexLinkMod2Triangle K v
  have hcard :
      (Finset.univ.filter (fun σ : T => f.1.InTriangle σ.1)).card = 2 := by
    let S := (vertexLinkTriangles K v).toFinset
    rw [Finset.card_filter, Finset.univ_eq_attach S]
    rw [Finset.sum_attach S (fun σ => if f.1.InTriangle σ then 1 else 0)]
    rw [← Finset.card_filter]
    change ((vertexLinkTriangles K v).toFinset.filter
      (fun σ => f.1.InTriangle σ)).card = 2
    have heq :
        (vertexLinkTriangles K v).toFinset.filter (fun σ => f.1.InTriangle σ) =
          ((vertexLinkTriangles K v).filter
            (fun σ => decide (f.1.InTriangle σ))).toFinset := by
      ext
      simp
    rw [heq]
    rw [List.toFinset_card_of_nodup]
    · exact hSurf.1.2.2.1 f.1 hrep
    · exact (vertexLinkTriangles_nodup K hcore v).filter _
  have hcenter (σ : T) (hs : f.1.InTriangle σ.1) :
      e ∈ σ.1.verts := by
    rcases hef with he | he
    · rw [he]
      exact hs.1
    · rw [he]
      exact hs.2
  simp only [vertexLinkMod2BoundaryTwo, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, vertexLinkMod2BoundaryTwoMatrix]
  change (∑ σ : T,
      (if f.1.InTriangle σ.1 then (1 : ZMod 2) else 0) *
        (if e ∈ σ.1.verts then (1 : ZMod 2) else 0)) = 0
  have hterm (σ : T) :
      (if f.1.InTriangle σ.1 then (1 : ZMod 2) else 0) *
          (if e ∈ σ.1.verts then (1 : ZMod 2) else 0) =
        (if f.1.InTriangle σ.1 then (1 : ZMod 2) else 0) := by
    by_cases hs : f.1.InTriangle σ.1
    · simp [hs, hcenter σ hs]
    · simp [hs]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp [hcard]

end Poincare
