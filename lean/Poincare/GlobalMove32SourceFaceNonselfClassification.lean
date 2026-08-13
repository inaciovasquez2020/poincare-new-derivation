import Poincare.GlobalMove32SourceFaceClassification
import Poincare.GlobalMove32SelfReentryNoDegreeFour

namespace Poincare

/--
A realized Move32 source-face obstruction in the no-degree-four manifold
branch either opens a legal Move23 move or produces a represented
complementary edge that is genuinely different, as an unordered edge,
from the original Move32 shared edge.
-/
theorem
    ClosedTriangulationCore.exists_legal_move23_or_nonself_complementEdge_of_move32_sourceFace_obstruction
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
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
        ¬ ((x = s.d ∧ y = s.e) ∨
           (x = s.e ∧ y = s.d)) := by

  rcases
      hcore.exists_legal_move23_or_complementEdge_of_move32_sourceFace_obstruction
        s
        hrealized
        hobstruction
    with hmove23 | hedge

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
        hySigma⟩

    have hnonself :
        ¬ ((x = s.d ∧ y = s.e) ∨
           (x = s.e ∧ y = s.d)) := by
      intro hself

      exact
        hcore.not_move32_complementEdge_self_reentry_of_no_degree_four
          hlinks
          hconn
          hNoFour
          s
          hrealized
          htauK
          hrhoK
          hne
          haTau
          hbTau
          hcTau
          haRho
          hbRho
          hcRho
          hxTau
          hxABC
          hyRho
          hyABC
          hself

    exact
      Or.inr
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

end Poincare
