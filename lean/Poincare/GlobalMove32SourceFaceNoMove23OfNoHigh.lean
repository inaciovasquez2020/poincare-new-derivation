import Poincare.GlobalMove32SourceFaceLegalMove23High

namespace Poincare

/-- In the no-degree-four source-face branch, excluding nonself high-edge
escape already excludes every legal Move23 aligned with the obstructed source
face.  Thus the older `hNoMove23` fail-closed hypothesis is derivable from
`hNoHigh`. -/
theorem ClosedTriangulationCore.no_matching_legal_move23_of_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ x y sigma,
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
                   y ∈ gamma.verts))).length) :
    ∀ s : Move32Site,
      s.RealizedIn K →
      (∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts) →
      ¬ ∃ m : Move23Site,
        m.a = s.a ∧
        m.b = s.b ∧
        m.c = s.c ∧
        m.LegalIn K := by
  classical
  intro s hrealized hobstruction
  rintro ⟨m, ha, hb, hc, hlegal⟩

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
    (hNoHigh s hrealized hobstruction)
      ⟨s.b, s.c, sigma, hbc, hsigmaK, hbSigma, hcSigma,
        hnonself, hhighCount⟩

end Poincare
