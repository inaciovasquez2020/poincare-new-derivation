import Poincare.GlobalMove32WitnessedSourceFaceReentry
import Poincare.Move32IndividualSourceNoDegreeFour
import Poincare.ComplementVertex

namespace Poincare

theorem ClosedTriangulationCore.witnessedReentry_next_sharedEdge_disjoint_previous_carrier_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (s t : Move32Site)
    (hrealized : s.RealizedIn K)
    (hstep : Move32SourceFaceWitnessedReentry K s t) :
    List.Disjoint [t.d, t.e] [s.a, s.b, s.c, s.d, s.e] := by
  classical
  rcases hstep with
    ⟨tau, rho, x, y, sigma, htauK, hrhoK, hne,
      haTau, hbTau, hcTau, haRho, hbRho, hcRho,
      hxTau, hxABC, hyRho, hyABC, hxy,
      hsigmaK, hxSigma, hySigma, hnonself, htd, hte,
      hrealizedT, hthreeT, hobstructionT⟩
  have hfive := hcore.move32Site_distinct s hrealized
  have habc : [s.a, s.b, s.c].Nodup := by
    simp at hfive ⊢
    aesop
  obtain ⟨u, v, huTau, huABC, hvRho, hvABC, huv, hTauCover, hRhoCover⟩ :=
    Tet.exists_distinct_complement_vertices tau rho
      (hcore.1 tau htauK) (hcore.1 rho hrhoK) habc
      haTau hbTau hcTau haRho hbRho hcRho hne
  have hxu : x = u := by
    have hc := hTauCover x hxTau
    simp at hxABC
    aesop
  have hyv : y = v := by
    have hc := hRhoCover y hyRho
    simp at hyABC
    aesop
  subst u
  subst v
  have sameOfCover (q : Nat) (zeta : Tet)
      (ha : s.a ∈ zeta.verts) (hb : s.b ∈ zeta.verts)
      (hc : s.c ∈ zeta.verts) (hq : q ∈ zeta.verts)
      (hcover : ∀ z ∈ zeta.verts, z = s.a ∨ z = s.b ∨ z = s.c ∨ z = q) :
      SameTetVertices zeta ⟨s.a, s.b, s.c, q⟩ := by
    intro z
    constructor
    · intro hz
      rcases hcover z hz with rfl | rfl | rfl | rfl <;> simp [Tet.verts]
    · intro hz
      simp [Tet.verts] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact hq
  have hsameTau := sameOfCover x tau haTau hbTau hcTau hxTau hTauCover
  have hsameRho := sameOfCover y rho haRho hbRho hcRho hyRho hRhoCover
  have hxD : x ≠ s.d := by
    intro h
    have hsource : ∃ zeta ∈ K.tets, SameTetVertices zeta s.sourceTet₀ := by
      refine ⟨tau, htauK, ?_⟩
      simpa [Move32Site.sourceTet₀, h, Tet.verts] using hsameTau
    have hsupp : s.d ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨tau, htauK, (hsameTau s.d).2 (by simp [h, Tet.verts])⟩
    exact hcore.not_move32_sourceTet0_represented_of_no_degree_four_of_connectedLink
      hNoFour s hrealized hsource (hlinks s.d hsupp)
  have hxE : x ≠ s.e := by
    intro h
    have hsource : ∃ zeta ∈ K.tets, SameTetVertices zeta s.sourceTet₁ := by
      refine ⟨tau, htauK, ?_⟩
      simpa [Move32Site.sourceTet₁, h, Tet.verts] using hsameTau
    have hsupp : s.e ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨tau, htauK, (hsameTau s.e).2 (by simp [h, Tet.verts])⟩
    exact hcore.not_move32_sourceTet1_represented_of_no_degree_four_of_connectedLink
      hNoFour s hrealized hsource (hlinks s.e hsupp)
  have hyD : y ≠ s.d := by
    intro h
    have hsource : ∃ zeta ∈ K.tets, SameTetVertices zeta s.sourceTet₀ := by
      refine ⟨rho, hrhoK, ?_⟩
      simpa [Move32Site.sourceTet₀, h, Tet.verts] using hsameRho
    have hsupp : s.d ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨rho, hrhoK, (hsameRho s.d).2 (by simp [h, Tet.verts])⟩
    exact hcore.not_move32_sourceTet0_represented_of_no_degree_four_of_connectedLink
      hNoFour s hrealized hsource (hlinks s.d hsupp)
  have hyE : y ≠ s.e := by
    intro h
    have hsource : ∃ zeta ∈ K.tets, SameTetVertices zeta s.sourceTet₁ := by
      refine ⟨rho, hrhoK, ?_⟩
      simpa [Move32Site.sourceTet₁, h, Tet.verts] using hsameRho
    have hsupp : s.e ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨rho, hrhoK, (hsameRho s.e).2 (by simp [h, Tet.verts])⟩
    exact hcore.not_move32_sourceTet1_represented_of_no_degree_four_of_connectedLink
      hNoFour s hrealized hsource (hlinks s.e hsupp)
  rw [List.disjoint_left]
  intro z hzT hzS
  simp at hzT hzS hxABC hyABC
  rcases hzT with h | h <;> rcases hzS with h' | h' | h' | h' | h'
  all_goals subst z
  all_goals simp_all

/-- A witnessed source-face reentry step carries seven distinct labels:
the five vertices of the previous Move32 carrier followed by both endpoints
of the next shared edge. -/
theorem ClosedTriangulationCore.witnessedReentry_seven_labels_nodup_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (s t : Move32Site)
    (hrealized : s.RealizedIn K)
    (hstep : Move32SourceFaceWitnessedReentry K s t) :
    [s.a, s.b, s.c, s.d, s.e, t.d, t.e].Nodup := by
  have hdisjoint :=
    hcore.witnessedReentry_next_sharedEdge_disjoint_previous_carrier_of_no_degree_four
      hlinks hNoFour s t hrealized hstep
  have hs := hcore.move32Site_distinct s hrealized
  have hrealizedT : t.RealizedIn K := hstep.toSourceFaceReentry.1
  have ht := hcore.move32Site_distinct t hrealizedT
  rw [List.disjoint_left] at hdisjoint
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdisjoint
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hs ht ⊢
  aesop

end Poincare
