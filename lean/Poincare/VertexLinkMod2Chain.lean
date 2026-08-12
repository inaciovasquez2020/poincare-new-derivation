import Poincare.VertexLink
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Poincare

abbrev VertexLinkMod2Vertex (K : Triangulation) (v : Nat) :=
  ↥((vertexLinkVertices K v).toFinset)

abbrev VertexLinkMod2Edge (K : Triangulation)
    (hcore : ClosedTriangulationCore K) (v : Nat) :=
  ↥((vertexLinkEdges K hcore v).toFinset)

abbrev VertexLinkMod2Triangle (K : Triangulation) (v : Nat) :=
  ↥((vertexLinkTriangles K v).toFinset)

def vertexLinkMod2BoundaryOneMatrix (K : Triangulation)
    (hcore : ClosedTriangulationCore K) (v : Nat) :
    Matrix
      (VertexLinkMod2Vertex K v)
      (VertexLinkMod2Edge K hcore v)
      (ZMod 2) :=
  fun x e =>
    if x.1 = e.1.lo ∨ x.1 = e.1.hi then 1 else 0

def vertexLinkMod2BoundaryTwoMatrix (K : Triangulation)
    (hcore : ClosedTriangulationCore K) (v : Nat) :
    Matrix
      (VertexLinkMod2Edge K hcore v)
      (VertexLinkMod2Triangle K v)
      (ZMod 2) :=
  fun e σ =>
    if e.1.InTriangle σ.1 then 1 else 0

def vertexLinkMod2BoundaryOne (K : Triangulation)
    (hcore : ClosedTriangulationCore K) (v : Nat) :=
  (vertexLinkMod2BoundaryOneMatrix K hcore v).mulVecLin

def vertexLinkMod2BoundaryTwo (K : Triangulation)
    (hcore : ClosedTriangulationCore K) (v : Nat) :=
  (vertexLinkMod2BoundaryTwoMatrix K hcore v).mulVecLin

def VertexLinkMod2H1Zero (K : Triangulation)
    (hcore : ClosedTriangulationCore K) (v : Nat) : Prop :=
  LinearMap.ker (vertexLinkMod2BoundaryOne K hcore v) =
    LinearMap.range (vertexLinkMod2BoundaryTwo K hcore v)

theorem vertexLinkMod2H1Zero_iff (K : Triangulation)
    (hcore : ClosedTriangulationCore K) (v : Nat) :
    VertexLinkMod2H1Zero K hcore v ↔
      LinearMap.ker (vertexLinkMod2BoundaryOne K hcore v) =
        LinearMap.range (vertexLinkMod2BoundaryTwo K hcore v) := by
  rfl

@[simp]
theorem LinkEdge.incident_ofDistinct_iff
    (a b x : Nat) (hab : a ≠ b) :
    (x = (LinkEdge.ofDistinct a b hab).lo ∨
      x = (LinkEdge.ofDistinct a b hab).hi) ↔
      x = a ∨ x = b := by
  unfold LinkEdge.ofDistinct
  split <;> simp [or_comm]

@[simp]
theorem LinkEdge.decide_incident_ofDistinct
    (a b x : Nat) (hab : a ≠ b) :
    (decide (x = (LinkEdge.ofDistinct a b hab).lo) ||
        decide (x = (LinkEdge.ofDistinct a b hab).hi)) =
      (decide (x = a) || decide (x = b)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact LinkEdge.incident_ofDistinct_iff a b x hab

theorem LinkTriangle.incident_edges_filter_length
    (σ : LinkTriangle)
    (hσ : σ.verts.Nodup)
    (x : Nat) :
    ((σ.edges hσ).filter
      (fun e => decide (x = e.lo ∨ x = e.hi))).length =
      if x ∈ σ.verts then 2 else 0 := by
  rcases σ with ⟨a, b, c⟩
  have h : (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by
    simpa [LinkTriangle.verts] using hσ
  rcases h with ⟨⟨hab, hac⟩, hbc⟩
  by_cases hxa : x = a
  · subst x
    simp only [LinkTriangle.edges, List.filter_cons,
      LinkEdge.decide_incident_ofDistinct, List.filter_nil]
    simp [LinkTriangle.verts, hab, hac, hbc]
  by_cases hxb : x = b
  · subst x
    simp only [LinkTriangle.edges, List.filter_cons,
      LinkEdge.decide_incident_ofDistinct, List.filter_nil]
    simp [LinkTriangle.verts, hxa, hab, hac, hbc]
  by_cases hxc : x = c
  · subst x
    simp only [LinkTriangle.edges, List.filter_cons,
      LinkEdge.decide_incident_ofDistinct, List.filter_nil]
    simp [LinkTriangle.verts, hxa, hxb, hab, hac, hbc]
  · simp only [LinkTriangle.edges, List.filter_cons,
      LinkEdge.decide_incident_ofDistinct, List.filter_nil]
    simp [LinkTriangle.verts, hxa, hxb, hxc]

theorem vertexLinkEdges_filter_inTriangle
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (σ : LinkTriangle)
    (hσmem : σ ∈ vertexLinkTriangles K v) :
    (vertexLinkEdges K hcore v).toFinset.filter
        (fun e => e.InTriangle σ) =
      (σ.edges
        (vertexLinkTriangles_triangle_nodup K hcore v σ hσmem)).toFinset := by
  classical
  apply Finset.ext
  intro e
  simp only [Finset.mem_filter, List.mem_toFinset]
  constructor
  · intro he
    exact LinkTriangle.inTriangle_mem_edges σ
      (vertexLinkTriangles_triangle_nodup K hcore v σ hσmem) e he.2
  · intro he
    have hin := LinkTriangle.mem_edges_inTriangle σ
      (vertexLinkTriangles_triangle_nodup K hcore v σ hσmem) e he
    exact ⟨represented_mem_vertexLinkEdges K hcore v e
      ⟨σ, hσmem, hin⟩, hin⟩

theorem vertexLinkMod2_boundary_one_comp_boundary_two
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat) :
    (vertexLinkMod2BoundaryOne K hcore v).comp
        (vertexLinkMod2BoundaryTwo K hcore v) =
      0 := by
  unfold vertexLinkMod2BoundaryOne vertexLinkMod2BoundaryTwo
  rw [← Matrix.mulVecLin_mul]
  rw [← Matrix.mulVecLin_zero]
  apply congrArg Matrix.mulVecLin
  ext x σ
  classical
  simp only [Matrix.mul_apply, vertexLinkMod2BoundaryOneMatrix,
    vertexLinkMod2BoundaryTwoMatrix]
  let S := (vertexLinkEdges K hcore v).toFinset
  change (∑ e : ↥S,
    (if x.1 = e.1.lo ∨ x.1 = e.1.hi then 1 else 0) *
      (if e.1.InTriangle σ.1 then 1 else 0)) = 0
  rw [Finset.univ_eq_attach S]
  rw [Finset.sum_attach S (fun e : LinkEdge =>
    (if x.1 = e.lo ∨ x.1 = e.hi then 1 else 0) *
      (if e.InTriangle σ.1 then 1 else 0))]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hσmem : σ.1 ∈ vertexLinkTriangles K v := by
    exact (List.mem_toFinset).1 σ.2
  rw [vertexLinkEdges_filter_inTriangle K hcore v σ.1 hσmem]
  rw [Finset.sum_boole]
  have hfilter :
      ((σ.1.edges
          (vertexLinkTriangles_triangle_nodup K hcore v σ.1 hσmem)).toFinset.filter
        (fun e => x.1 = e.lo ∨ x.1 = e.hi)) =
      (((σ.1.edges
          (vertexLinkTriangles_triangle_nodup K hcore v σ.1 hσmem)).filter
        (fun e => decide (x.1 = e.lo ∨ x.1 = e.hi))).toFinset) := by
    ext e
    simp
  rw [hfilter]
  rw [List.toFinset_card_of_nodup]
  · rw [LinkTriangle.incident_edges_filter_length]
    split <;> rfl
  · exact (LinkTriangle.edges_nodup σ.1
      (vertexLinkTriangles_triangle_nodup K hcore v σ.1 hσmem)).filter _

end Poincare
