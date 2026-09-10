import Poincare.GlobalMove32SourceFaceSourceEdgeHigh
import Mathlib.Tactic

namespace Poincare

/-- In the no-degree-four branch, a represented Move32 source face forces all
three source-face edges to have ambient tetrahedron incidence at least four.

The existing theorem proves this for `a-b`.  The `a-c` and `b-c` cases follow
by permuting the three source labels; `RealizedIn` is unchanged up to a
permutation of the three target tetrahedra, and the represented source-face
obstruction is unchanged as an unordered face. -/
theorem
    ClosedTriangulationCore.move32_all_sourceEdges_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hobstruction :
      ∃ theta ∈ K.tets,
        s.a ∈ theta.verts ∧
        s.b ∈ theta.verts ∧
        s.c ∈ theta.verts) :
    4 ≤
        (K.tets.filter
          (fun gamma =>
            s.a ∈ gamma.verts ∧
            s.b ∈ gamma.verts)).length ∧
    4 ≤
        (K.tets.filter
          (fun gamma =>
            s.a ∈ gamma.verts ∧
            s.c ∈ gamma.verts)).length ∧
    4 ≤
        (K.tets.filter
          (fun gamma =>
            s.b ∈ gamma.verts ∧
            s.c ∈ gamma.verts)).length := by
  classical

  have hab :=
    hcore.move32_sourceEdge_ab_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
      hlinks hNoFour s hrealized hobstruction

  rcases hrealized with
    ⟨⟨tau0, htau0, hsame0⟩,
      ⟨tau1, htau1, hsame1⟩,
      ⟨tau2, htau2, hsame2⟩⟩

  obtain ⟨theta, htheta, haTheta, hbTheta, hcTheta⟩ := hobstruction

  let sac : Move32Site :=
    {
      a := s.a
      b := s.c
      c := s.b
      d := s.d
      e := s.e
    }

  have hrealizedAC : sac.RealizedIn K := by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨tau1, htau1, ?_⟩
      intro z
      simpa [sac, Move32Site.targetTet₀, Move32Site.targetTet₁,
        Tet.verts, or_assoc, or_left_comm, or_comm] using hsame1 z
    · refine ⟨tau0, htau0, ?_⟩
      intro z
      simpa [sac, Move32Site.targetTet₀, Move32Site.targetTet₁,
        Tet.verts, or_assoc, or_left_comm, or_comm] using hsame0 z
    · refine ⟨tau2, htau2, ?_⟩
      intro z
      simpa [sac, Move32Site.targetTet₂,
        Tet.verts, or_assoc, or_left_comm, or_comm] using hsame2 z

  have hobstructionAC :
      ∃ theta ∈ K.tets,
        sac.a ∈ theta.verts ∧
        sac.b ∈ theta.verts ∧
        sac.c ∈ theta.verts := by
    exact ⟨theta, htheta, haTheta, hcTheta, hbTheta⟩

  have hac :=
    hcore.move32_sourceEdge_ab_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
      hlinks hNoFour sac hrealizedAC hobstructionAC

  let sbc : Move32Site :=
    {
      a := s.b
      b := s.c
      c := s.a
      d := s.d
      e := s.e
    }

  have hrealizedBC : sbc.RealizedIn K := by
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨tau2, htau2, ?_⟩
      intro z
      simpa [sbc, Move32Site.targetTet₀, Move32Site.targetTet₂,
        Tet.verts, or_assoc, or_left_comm, or_comm] using hsame2 z
    · refine ⟨tau0, htau0, ?_⟩
      intro z
      simpa [sbc, Move32Site.targetTet₀, Move32Site.targetTet₁,
        Tet.verts, or_assoc, or_left_comm, or_comm] using hsame0 z
    · refine ⟨tau1, htau1, ?_⟩
      intro z
      simpa [sbc, Move32Site.targetTet₁, Move32Site.targetTet₂,
        Tet.verts, or_assoc, or_left_comm, or_comm] using hsame1 z

  have hobstructionBC :
      ∃ theta ∈ K.tets,
        sbc.a ∈ theta.verts ∧
        sbc.b ∈ theta.verts ∧
        sbc.c ∈ theta.verts := by
    exact ⟨theta, htheta, hbTheta, hcTheta, haTheta⟩

  have hbc :=
    hcore.move32_sourceEdge_ab_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
      hlinks hNoFour sbc hrealizedBC hobstructionBC

  refine ⟨hab, ?_, ?_⟩
  · simpa [sac] using hac
  · simpa [sbc] using hbc

end Poincare
