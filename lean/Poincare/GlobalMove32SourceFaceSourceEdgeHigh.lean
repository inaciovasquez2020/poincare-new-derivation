import Poincare.GlobalMove32IncidenceThreeCandidate
import Poincare.GlobalRepresentedEdgeIncidenceSplit
import Poincare.Move32IndividualSourceNoDegreeFour
import Poincare.Move32SurvivorClassification
import Mathlib.Tactic

namespace Poincare

private theorem sameTetVertices_of_four_distinct_mem
    (tau : Tet)
    (a b c d : Nat)
    (htau : tau.verts.Nodup)
    (habcd : [a, b, c, d].Nodup)
    (ha : a ∈ tau.verts)
    (hb : b ∈ tau.verts)
    (hc : c ∈ tau.verts)
    (hd : d ∈ tau.verts) :
    SameTetVertices tau ⟨a, b, c, d⟩ := by
  classical

  let S : Finset Nat := tau.verts.toFinset
  let T : Finset Nat := [a, b, c, d].toFinset

  have hsub : T ⊆ S := by
    intro z hz
    have hz' : z ∈ [a, b, c, d] := by
      exact List.mem_toFinset.mp hz
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hz'
    apply List.mem_toFinset.mpr
    rcases hz' with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd

  have hScard : S.card = 4 := by
    dsimp [S]
    rw [List.toFinset_card_of_nodup htau]
    simp [Tet.verts]

  have hTcard : T.card = 4 := by
    dsimp [T]
    rw [List.toFinset_card_of_nodup habcd]
    simp

  have hEq : T = S :=
    Finset.eq_of_subset_of_card_le hsub (by omega)

  intro z
  constructor
  · intro hz
    have hzS : z ∈ S := List.mem_toFinset.mpr hz
    rw [← hEq] at hzS
    have hzT : z ∈ [a, b, c, d] := List.mem_toFinset.mp hzS
    simpa [Tet.verts] using hzT
  · intro hz
    have hzT : z ∈ [a, b, c, d] := by
      simpa [Tet.verts] using hz
    have hzFin : z ∈ T := List.mem_toFinset.mpr hzT
    rw [hEq] at hzFin
    exact List.mem_toFinset.mp hzFin

/--
In the no-degree-four branch, a represented Move32 source face already forces
one of its source edges to have ambient tetrahedron incidence at least four.

The proof uses the edge `a-b`.  If its incidence were exactly three, the
opposite link triangles contributed by the represented target tetrahedron
`{a,b,d,e}` and by the source-face obstruction tetrahedron would be two
members of the same three-triangle edge star.  The exact-three star normal
form forces any two distinct members to share a second link vertex.  On the
target side that vertex must be `d` or `e`, whereas the no-degree-four source
tetrahedron exclusions forbid either `d` or `e` from lying in the obstruction
tetrahedron.  Hence exact incidence three is impossible.
-/
theorem ClosedTriangulationCore.move32_sourceEdge_ab_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
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
          s.b ∈ gamma.verts)).length := by
  classical

  have hfive :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hrealized

  have hab : s.a ≠ s.b := by
    have h := hfive
    simp at h
    aesop

  have hba : s.b ≠ s.a := Ne.symm hab

  have hca : s.c ≠ s.a := by
    have h := hfive
    simp at h
    aesop

  have habc : [s.a, s.b, s.c].Nodup := by
    have h := hfive
    simp at h ⊢
    aesop

  have habcd : [s.a, s.b, s.c, s.d].Nodup := by
    have h := hfive
    simp at h ⊢
    aesop

  have habce : [s.a, s.b, s.c, s.e].Nodup := by
    have h := hfive
    simp at h ⊢
    aesop

  obtain ⟨theta, hthetaK, haTheta, hbTheta, hcTheta⟩ := hobstruction

  have hthetaNodup : theta.verts.Nodup := hcore.1 theta hthetaK

  have hdTheta : s.d ∉ theta.verts := by
    intro hd
    have hsame : SameTetVertices theta s.sourceTet₀ := by
      simpa [Move32Site.sourceTet₀] using
        sameTetVertices_of_four_distinct_mem
          theta s.a s.b s.c s.d
          hthetaNodup habcd haTheta hbTheta hcTheta hd
    have hsource :
        ∃ tau ∈ K.tets, SameTetVertices tau s.sourceTet₀ :=
      ⟨theta, hthetaK, hsame⟩
    have hdSupport : s.d ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨theta, hthetaK, hd⟩
    exact
      hcore.not_move32_sourceTet0_represented_of_no_degree_four_of_connectedLink
        hNoFour s hrealized hsource
        (hlinks s.d hdSupport)

  have heTheta : s.e ∉ theta.verts := by
    intro he
    have hsame : SameTetVertices theta s.sourceTet₁ := by
      simpa [Move32Site.sourceTet₁] using
        sameTetVertices_of_four_distinct_mem
          theta s.a s.b s.c s.e
          hthetaNodup habce haTheta hbTheta hcTheta he
    have hsource :
        ∃ tau ∈ K.tets, SameTetVertices tau s.sourceTet₁ :=
      ⟨theta, hthetaK, hsame⟩
    have heSupport : s.e ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨theta, hthetaK, he⟩
    exact
      hcore.not_move32_sourceTet1_represented_of_no_degree_four_of_connectedLink
        hNoFour s hrealized hsource
        (hlinks s.e heSupport)

  obtain ⟨t0, ht0K, ht0⟩ := hrealized.1

  have haT0 : s.a ∈ t0.verts := by
    apply (ht0 s.a).2
    simp [Move32Site.targetTet₀, Tet.verts]

  have hbT0 : s.b ∈ t0.verts := by
    apply (ht0 s.b).2
    simp [Move32Site.targetTet₀, Tet.verts]

  have hcNotT0 : s.c ∉ t0.verts := by
    intro hc
    have hcTarget : s.c ∈ s.targetTet₀.verts := (ht0 s.c).1 hc
    have h := hfive
    simp [Move32Site.targetTet₀, Tet.verts] at hcTarget
    simp at h
    aesop

  have ht0Edge :
      t0 ∈
        K.tets.filter
          (fun gamma =>
            s.a ∈ gamma.verts ∧
            s.b ∈ gamma.verts) := by
    simp [ht0K, haT0, hbT0]

  have hpos :
      0 <
        (K.tets.filter
          (fun gamma =>
            s.a ∈ gamma.verts ∧
            s.b ∈ gamma.verts)).length :=
    List.length_pos_iff_exists_mem.mpr ⟨t0, ht0Edge⟩

  rcases hcore.edgeIncidence_eq_three_or_four_le_of_pos
      s.a s.b hab hpos with hthree | hhigh
  · exfalso

    obtain ⟨sigmaT, hSigmaTLink, hExtractT⟩ :=
      exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
        K s.a t0 ht0K haT0

    obtain ⟨sigmaS, hSigmaSLink, hExtractS⟩ :=
      exists_vertexLinkTriangle_of_tet_mem_of_vertex_mem
        K s.a theta hthetaK haTheta

    have hbSigmaT : s.b ∈ sigmaT.verts :=
      (t0.mem_linkTriangleAt?_iff
        s.a s.b sigmaT hExtractT hba).2 hbT0

    have hbSigmaS : s.b ∈ sigmaS.verts :=
      (theta.mem_linkTriangleAt?_iff
        s.a s.b sigmaS hExtractS hba).2 hbTheta

    have hcSigmaS : s.c ∈ sigmaS.verts :=
      (theta.mem_linkTriangleAt?_iff
        s.a s.c sigmaS hExtractS hca).2 hcTheta

    have hSigmaNe : sigmaT ≠ sigmaS := by
      intro hEq
      have hcSigmaT : s.c ∈ sigmaT.verts := by
        simpa [hEq] using hcSigmaS
      exact hcNotT0
        (t0.linkTriangleAt?_verts_subset
          s.a sigmaT hExtractT s.c hcSigmaT)

    have hSigmaTStar :
        sigmaT ∈ vertexLinkStarTriangles K s.a s.b :=
      (mem_vertexLinkStarTriangles_iff
        K s.a s.b sigmaT).2 ⟨hSigmaTLink, hbSigmaT⟩

    have hSigmaSStar :
        sigmaS ∈ vertexLinkStarTriangles K s.a s.b :=
      (mem_vertexLinkStarTriangles_iff
        K s.a s.b sigmaS).2 ⟨hSigmaSLink, hbSigmaS⟩

    obtain ⟨sigma0, sigma1, sigma2, p, q, r,
      h0Link, h1Link, h2Link,
      hpB, hqB, hrB,
      hpq, hpr, hqr,
      hsup0, hsup1, hsup2⟩ :=
      hcore.exists_incidenceThree_vertexLink_support_normalForm
        s.a s.b hab hthree

    have hb0 : s.b ∈ sigma0.verts :=
      (hsup0 s.b).2 (Or.inl rfl)
    have hb1 : s.b ∈ sigma1.verts :=
      (hsup1 s.b).2 (Or.inl rfl)
    have hb2 : s.b ∈ sigma2.verts :=
      (hsup2 s.b).2 (Or.inl rfl)

    have h0Star : sigma0 ∈ vertexLinkStarTriangles K s.a s.b :=
      (mem_vertexLinkStarTriangles_iff K s.a s.b sigma0).2 ⟨h0Link, hb0⟩
    have h1Star : sigma1 ∈ vertexLinkStarTriangles K s.a s.b :=
      (mem_vertexLinkStarTriangles_iff K s.a s.b sigma1).2 ⟨h1Link, hb1⟩
    have h2Star : sigma2 ∈ vertexLinkStarTriangles K s.a s.b :=
      (mem_vertexLinkStarTriangles_iff K s.a s.b sigma2).2 ⟨h2Link, hb2⟩

    have h01 : sigma0 ≠ sigma1 := by
      intro hEq
      have hq0 : q ∈ sigma0.verts :=
        (hsup0 q).2 (Or.inr (Or.inr rfl))
      have hq1 : q ∈ sigma1.verts := by simpa [hEq] using hq0
      have hqCases := (hsup1 q).1 hq1
      aesop

    have h02 : sigma0 ≠ sigma2 := by
      intro hEq
      have hp0 : p ∈ sigma0.verts :=
        (hsup0 p).2 (Or.inr (Or.inl rfl))
      have hp2 : p ∈ sigma2.verts := by simpa [hEq] using hp0
      have hpCases := (hsup2 p).1 hp2
      aesop

    have h12 : sigma1 ≠ sigma2 := by
      intro hEq
      have hp1 : p ∈ sigma1.verts :=
        (hsup1 p).2 (Or.inr (Or.inl rfl))
      have hp2 : p ∈ sigma2.verts := by simpa [hEq] using hp1
      have hpCases := (hsup2 p).1 hp2
      aesop

    have hstarLen :
        (vertexLinkStarTriangles K s.a s.b).length = 3 :=
      hcore.vertexLinkStarTriangles_length_eq_three_of_edgeIncidence_three
        s.a s.b hab hthree

    have hTcase :
        sigmaT = sigma0 ∨ sigmaT = sigma1 ∨ sigmaT = sigma2 :=
      eq_one_of_three_of_mem_of_length_eq_three
        hstarLen h0Star h1Star h2Star h01 h02 h12 hSigmaTStar

    have hScase :
        sigmaS = sigma0 ∨ sigmaS = sigma1 ∨ sigmaS = sigma2 :=
      eq_one_of_three_of_mem_of_length_eq_three
        hstarLen h0Star h1Star h2Star h01 h02 h12 hSigmaSStar

    have hcommon :
        ∃ y : Nat,
          y ≠ s.b ∧
          y ∈ sigmaT.verts ∧
          y ∈ sigmaS.verts := by
      rcases hTcase with hT0 | hT1 | hT2
      · rcases hScase with hS0 | hS1 | hS2
        · exact (hSigmaNe (hT0.trans hS0.symm)).elim
        · refine ⟨p, hpB, ?_, ?_⟩
          · rw [hT0]
            exact (hsup0 p).2 (Or.inr (Or.inl rfl))
          · rw [hS1]
            exact (hsup1 p).2 (Or.inr (Or.inl rfl))
        · refine ⟨q, hqB, ?_, ?_⟩
          · rw [hT0]
            exact (hsup0 q).2 (Or.inr (Or.inr rfl))
          · rw [hS2]
            exact (hsup2 q).2 (Or.inr (Or.inl rfl))
      · rcases hScase with hS0 | hS1 | hS2
        · refine ⟨p, hpB, ?_, ?_⟩
          · rw [hT1]
            exact (hsup1 p).2 (Or.inr (Or.inl rfl))
          · rw [hS0]
            exact (hsup0 p).2 (Or.inr (Or.inl rfl))
        · exact (hSigmaNe (hT1.trans hS1.symm)).elim
        · refine ⟨r, hrB, ?_, ?_⟩
          · rw [hT1]
            exact (hsup1 r).2 (Or.inr (Or.inr rfl))
          · rw [hS2]
            exact (hsup2 r).2 (Or.inr (Or.inr rfl))
      · rcases hScase with hS0 | hS1 | hS2
        · refine ⟨q, hqB, ?_, ?_⟩
          · rw [hT2]
            exact (hsup2 q).2 (Or.inr (Or.inl rfl))
          · rw [hS0]
            exact (hsup0 q).2 (Or.inr (Or.inr rfl))
        · refine ⟨r, hrB, ?_, ?_⟩
          · rw [hT2]
            exact (hsup2 r).2 (Or.inr (Or.inr rfl))
          · rw [hS1]
            exact (hsup1 r).2 (Or.inr (Or.inr rfl))
        · exact (hSigmaNe (hT2.trans hS2.symm)).elim

    obtain ⟨y, hyB, hyT, hyS⟩ := hcommon

    have hyT0 : y ∈ t0.verts :=
      t0.linkTriangleAt?_verts_subset s.a sigmaT hExtractT y hyT

    have hyTheta : y ∈ theta.verts :=
      theta.linkTriangleAt?_verts_subset s.a sigmaS hExtractS y hyS

    have hyA : y ≠ s.a := by
      intro h
      subst y
      exact
        (t0.linkTriangleAt?_vertex_not_mem
          s.a sigmaT (hcore.1 t0 ht0K) hExtractT) hyT

    have hyTarget : y ∈ s.targetTet₀.verts := (ht0 y).1 hyT0

    have hyDE : y = s.d ∨ y = s.e := by
      simp [Move32Site.targetTet₀, Tet.verts] at hyTarget
      aesop

    rcases hyDE with rfl | rfl
    · exact hdTheta hyTheta
    · exact heTheta hyTheta

  · exact hhigh

end Poincare