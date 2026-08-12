import Poincare.VertexLink
import Mathlib.Tactic

namespace Poincare

private theorem mem_vertexSupport_iff_vertexDegree_pos_local
    (K : Triangulation)
    (v : Nat) :
    v ∈ vertexSupport K ↔
      0 < vertexDegree K v := by
  rw [mem_vertexSupport_iff]
  change
    v ∈ allVerts K ↔
      0 < (allVerts K).count v
  simpa using
    ((Multiset.count_pos
      (a := v)
      (s := (↑(allVerts K) : Multiset Nat))).symm)

/--
Every represented vertex of a closed triangulation core has ambient
tetrahedron degree at least four.
-/
theorem ClosedTriangulationCore.vertexDegree_ge_four_of_mem_vertexSupport
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v : Nat}
    (hv : v ∈ vertexSupport K) :
    4 ≤ vertexDegree K v := by

  have hpos :
      0 < vertexDegree K v :=
    (mem_vertexSupport_iff_vertexDegree_pos_local
      K v).1 hv

  have hfaces :
      (vertexLinkTriangles K v).length =
        vertexDegree K v :=
    vertexLinkTriangles_length_eq_vertexDegree
      K hcore v

  cases hlink :
      vertexLinkTriangles K v with

  | nil =>
      rw [hlink] at hfaces
      simp at hfaces
      omega

  | cons σ rest =>
      have hσ :
          σ ∈ vertexLinkTriangles K v := by
        rw [hlink]
        simp

      have hrep :
          VertexLinkVertexRepresented K v σ.v0 := by
        refine ⟨σ, hσ, ?_⟩
        simp [LinkTriangle.verts]

      have hstarDegree :
          VertexLinkStarDegreeTwo K v σ.v0 :=
        hcore.vertexLinkStarDegreeTwo hrep

      have hstarThree :
          3 ≤
            (vertexLinkStarTriangles
              K v σ.v0).length :=
        represented_star_length_ge_three
          K hcore v σ.v0
          hrep
          hstarDegree

      have hstarLe :
          (vertexLinkStarTriangles
            K v σ.v0).length ≤
          (vertexLinkTriangles K v).length := by
        unfold vertexLinkStarTriangles
        exact List.length_filter_le _ _

      have hdegreeThree :
          3 ≤ vertexDegree K v := by
        rw [← hfaces]
        exact le_trans hstarThree hstarLe

      have hincidence :=
        vertexLink_three_mul_faces_eq_two_mul_edges
          K hcore v

      rw [hfaces] at hincidence

      omega

/--
Closed-core vertex degrees have a genuine gap:
a represented vertex has degree exactly four or degree at least six.
In particular ambient degree five cannot occur.
-/
theorem ClosedTriangulationCore.vertexDegree_eq_four_or_ge_six_of_mem_vertexSupport
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v : Nat}
    (hv : v ∈ vertexSupport K) :
    vertexDegree K v = 4 ∨
      6 ≤ vertexDegree K v := by

  have hfour :
      4 ≤ vertexDegree K v :=
    hcore.vertexDegree_ge_four_of_mem_vertexSupport hv

  have hincidence :=
    vertexLink_three_mul_faces_eq_two_mul_edges
      K hcore v

  rw [
    vertexLinkTriangles_length_eq_vertexDegree
      K hcore v
  ] at hincidence

  by_cases hdeg4 :
      vertexDegree K v = 4

  · exact Or.inl hdeg4

  · right
    omega

/--
If a represented closed-core vertex is not degree four, it is automatically
degree at least six.
-/
theorem ClosedTriangulationCore.vertexDegree_ge_six_of_mem_vertexSupport_of_ne_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v : Nat}
    (hv : v ∈ vertexSupport K)
    (hne :
      vertexDegree K v ≠ 4) :
    6 ≤ vertexDegree K v := by

  rcases
    hcore.vertexDegree_eq_four_or_ge_six_of_mem_vertexSupport hv
    with hfour | hsix

  · exact (hne hfour).elim
  · exact hsix

/--
A closed core with no degree-four represented vertex has degree at least six
at every represented vertex.
-/
theorem ClosedTriangulationCore.all_supported_vertexDegrees_ge_six_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4) :
    ∀ v ∈ vertexSupport K,
      6 ≤ vertexDegree K v := by

  intro v hv

  exact
    hcore.vertexDegree_ge_six_of_mem_vertexSupport_of_ne_four
      hv
      (hNoFour v hv)

end Poincare
