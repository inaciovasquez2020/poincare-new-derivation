import Poincare.GlobalMove32SourceFaceNonselfIncidenceSplit
import Poincare.GlobalMove32IncidenceThreeComposition

namespace Poincare

/--
One exact reentry step for a represented Move32 source-face obstruction in
the no-degree-four branch.

The obstruction yields one of four certified alternatives:

1. a genuine legal Move23 site;
2. an immediate topology-preserving strict PhiSupport descent;
3. a genuinely nonself represented complementary edge of incidence at least
   four;
4. a new realized incidence-three Move32 source-face obstruction whose shared
   edge is genuinely different from the original Move32 shared edge.

No termination statement for repeated reentry is made here.
-/
theorem
    ClosedTriangulationCore.exists_legal_move23_or_descent_or_nonself_complementEdge_high_or_reentry_of_move32_sourceFace_obstruction
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
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∃ x y sigma,
      x ≠ y ∧
      sigma ∈ K.tets ∧
      x ∈ sigma.verts ∧
      y ∈ sigma.verts ∧
      ¬ (
        (x = s.d ∧ y = s.e) ∨
        (x = s.e ∧ y = s.d)
      ) ∧
      4 ≤
        (K.tets.filter
          (fun gamma =>
            decide
              (x ∈ gamma.verts ∧
               y ∈ gamma.verts))).length) ∨
    ∃ s' : Move32Site,
      s'.RealizedIn K ∧
      s'.SharedEdgeExactlyThree K ∧
      (∃ tau ∈ K.tets,
        s'.a ∈ tau.verts ∧
        s'.b ∈ tau.verts ∧
        s'.c ∈ tau.verts) ∧
      ¬ (
        (s'.d = s.d ∧ s'.e = s.e) ∨
        (s'.d = s.e ∧ s'.e = s.d)
      ) := by
  classical

  rcases
      hcore.exists_legal_move23_or_nonself_complementEdge_incidence_split_of_move32_sourceFace_obstruction
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
        hnonself,
        hsplit⟩

    rcases hsplit with
      hthree | hhigh

    · rcases
          hcore.exists_descent_or_realized_sourceFace_obstruction_of_edgeIncidence_three
            hNoFour
            x
            y
            hxy
            hthree with
        hdesc | hreentry

      · exact
          Or.inr
            (Or.inl hdesc)

      · rcases hreentry with
          ⟨s',
            hsd,
            hse,
            hrealized',
            hthree',
            hobstruction'⟩

        have hnonself' :
            ¬ (
              (s'.d = s.d ∧
               s'.e = s.e) ∨
              (s'.d = s.e ∧
               s'.e = s.d)
            ) := by
          intro hself

          apply hnonself

          rcases hself with
            hdirect | hreverse

          · exact
              Or.inl
                ⟨hsd.symm.trans hdirect.1,
                  hse.symm.trans hdirect.2⟩

          · exact
              Or.inr
                ⟨hsd.symm.trans hreverse.1,
                  hse.symm.trans hreverse.2⟩

        exact
          Or.inr
            (Or.inr
              (Or.inr
                ⟨s',
                  hrealized',
                  hthree',
                  hobstruction',
                  hnonself'⟩))

    · exact
        Or.inr
          (Or.inr
            (Or.inl
              ⟨x,
                y,
                sigma,
                hxy,
                hsigmaK,
                hxSigma,
                hySigma,
                hnonself,
                hhigh⟩))

end Poincare
