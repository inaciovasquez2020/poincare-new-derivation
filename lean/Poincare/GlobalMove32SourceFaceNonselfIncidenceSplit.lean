import Poincare.GlobalMove32SourceFaceNonselfClassification
import Poincare.GlobalRepresentedEdgeIncidenceSplit

namespace Poincare

/--
In the no-degree-four branch, an incidence-three Move32 source-face
obstruction has an exact next classification.

Either the obstructing face yields a genuine legal `2 → 3` move, or its
represented complementary edge is genuinely different from the original
Move32 shared edge and has ambient tetrahedron incidence exactly three or at
least four.
-/
theorem
    ClosedTriangulationCore.exists_legal_move23_or_nonself_complementEdge_incidence_split_of_move32_sourceFace_obstruction
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn :
      TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hobstruction :
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts) :
    (∃ m : Move23Site,
      m.a = s.a ∧
      m.b = s.b ∧
      m.c = s.c ∧
      m.LegalIn K) ∨
    ∃ tau rho x y sigma,
      tau ∈ K.tets ∧
      rho ∈ K.tets ∧
      ¬ SameTetVertices tau rho ∧
      s.a ∈ tau.verts ∧
      s.b ∈ tau.verts ∧
      s.c ∈ tau.verts ∧
      s.a ∈ rho.verts ∧
      s.b ∈ rho.verts ∧
      s.c ∈ rho.verts ∧
      x ∈ tau.verts ∧
      x ∉ [s.a, s.b, s.c] ∧
      y ∈ rho.verts ∧
      y ∉ [s.a, s.b, s.c] ∧
      x ≠ y ∧
      sigma ∈ K.tets ∧
      x ∈ sigma.verts ∧
      y ∈ sigma.verts ∧
      ¬ (
        (x = s.d ∧ y = s.e) ∨
        (x = s.e ∧ y = s.d)
      ) ∧
      (
        (K.tets.filter
          (fun gamma =>
            x ∈ gamma.verts ∧
            y ∈ gamma.verts)).length = 3 ∨
        4 ≤
          (K.tets.filter
            (fun gamma =>
              x ∈ gamma.verts ∧
              y ∈ gamma.verts)).length
      ) := by
  classical

  rcases
      hcore.exists_legal_move23_or_nonself_complementEdge_of_move32_sourceFace_obstruction
        hlinks
        hconn
        hNoFour
        s
        hrealized
        hobstruction with
    hmove23 | hedge

  · exact Or.inl hmove23

  · rcases hedge with
      ⟨tau, rho, x, y, sigma,
        htauK,
        hrhoK,
        hne,
        haTau,
        hbTau,
        hcTau,
        haRho,
        hbRho,
        hcRho,
        hxTau,
        hxABC,
        hyRho,
        hyABC,
        hxy,
        hsigmaK,
        hxSigma,
        hySigma,
        hnonself⟩

    have hsigmaFilter :
        sigma ∈
          K.tets.filter
            (fun gamma =>
              x ∈ gamma.verts ∧
              y ∈ gamma.verts) := by
      simp [
        hsigmaK,
        hxSigma,
        hySigma
      ]

    have hpos :
        0 <
          (K.tets.filter
            (fun gamma =>
              x ∈ gamma.verts ∧
              y ∈ gamma.verts)).length := by
      exact
        List.length_pos_iff_exists_mem.mpr
          ⟨sigma, hsigmaFilter⟩

    have hsplit :
        (K.tets.filter
          (fun gamma =>
            x ∈ gamma.verts ∧
            y ∈ gamma.verts)).length = 3 ∨
        4 ≤
          (K.tets.filter
            (fun gamma =>
              x ∈ gamma.verts ∧
              y ∈ gamma.verts)).length :=
      hcore.edgeIncidence_eq_three_or_four_le_of_pos
        x
        y
        hxy
        hpos

    exact Or.inr
      ⟨tau, rho, x, y, sigma,
        htauK,
        hrhoK,
        hne,
        haTau,
        hbTau,
        hcTau,
        haRho,
        hbRho,
        hcRho,
        hxTau,
        hxABC,
        hyRho,
        hyABC,
        hxy,
        hsigmaK,
        hxSigma,
        hySigma,
        hnonself,
        hsplit⟩

end Poincare
