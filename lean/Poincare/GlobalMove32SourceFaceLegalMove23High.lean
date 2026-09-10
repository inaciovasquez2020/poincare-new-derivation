import Poincare.GlobalMove32WitnessedSourceFaceReentry
import Poincare.GlobalMove32TargetTet2PartnerSeparation

namespace Poincare

/-- In the no-degree-four source-face obstruction classification, the aligned
legal Move23 alternative is already a nonself high-edge alternative: its
`(b,c)` edge has incidence at least five.  Thus the four-way source-face fork
collapses to descent, a nonself edge of incidence at least four, or witnessed
reentry. -/
theorem
    ClosedTriangulationCore.exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
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
      ¬ ((x = s.d ∧ y = s.e) ∨
         (x = s.e ∧ y = s.d)) ∧
      4 ≤
        (K.tets.filter
          (fun gamma =>
            decide
              (x ∈ gamma.verts ∧
               y ∈ gamma.verts))).length) ∨
    ∃ s' : Move32Site,
      Move32SourceFaceWitnessedReentry K s s' := by
  classical
  rcases
      hcore.exists_legal_move23_or_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
        hlinks hconn hNoFour s hrealized hobstruction with
    hmove23 | hdesc | hhigh | hreentry
  · obtain ⟨m, ha, hb, hc, hlegal⟩ := hmove23
    obtain ⟨sigma, hsigmaK, hsame⟩ := hrealized.2.2
    have hbSigma : s.b ∈ sigma.verts :=
      (hsame s.b).2 (by simp [Move32Site.targetTet₂, Tet.verts])
    have hcSigma : s.c ∈ sigma.verts :=
      (hsame s.c).2 (by simp [Move32Site.targetTet₂, Tet.verts])
    have hfive := hcore.move32Site_distinct s hrealized
    have hbc : s.b ≠ s.c := by
      have h := hfive
      simp at h
      aesop
    have hnonself :
        ¬ ((s.b = s.d ∧ s.c = s.e) ∨
           (s.b = s.e ∧ s.c = s.d)) := by
      have h := hfive
      simp at h
      aesop
    have hfiveCount :=
      m.five_le_bc_edgeIncidence_of_sourceFace_alignment_of_no_degree_four
        s hcore hlinks hNoFour hrealized ha hb hc hlegal
    have hhighCount :
        4 ≤
          (K.tets.filter
            (fun gamma =>
              decide
                (s.b ∈ gamma.verts ∧
                 s.c ∈ gamma.verts))).length := by
      have hfiveCount' :
          5 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (s.b ∈ gamma.verts ∧
                   s.c ∈ gamma.verts))).length := by
        simpa [hb, hc] using hfiveCount
      omega
    exact
      Or.inr
        (Or.inl
          ⟨s.b, s.c, sigma, hbc, hsigmaK, hbSigma, hcSigma,
            hnonself, hhighCount⟩)
  · exact Or.inl hdesc
  · exact Or.inr (Or.inl hhigh)
  · exact Or.inr (Or.inr hreentry)

end Poincare
