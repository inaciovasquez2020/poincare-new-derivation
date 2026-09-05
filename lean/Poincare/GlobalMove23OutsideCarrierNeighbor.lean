import Poincare.GlobalMove32CarrierPairRepresented
import Poincare.GlobalMove32IncidenceThreeCandidate
import Poincare.Move23ClosedCorePreservation
import Poincare.Move32IndividualSourceNoDegreeFour

namespace Poincare

/-- A legal `2 → 3` move relative to a realized `3 → 2` carrier has an
honest represented tetrahedron containing the shared face and an endpoint
outside the five-label carrier. -/
theorem Move23Site.exists_represented_neighbor_containing_outside_endpoint
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hrealized : s.RealizedIn K) (hlegal : m.LegalIn K) :
    (∃ tau ∈ K.tets,
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts ∧ m.c ∈ tau.verts ∧
        m.d ∈ tau.verts ∧
        m.d ∉ [s.a, s.b, s.c, s.d, s.e]) ∨
      (∃ tau ∈ K.tets,
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts ∧ m.c ∈ tau.verts ∧
        m.e ∈ tau.verts ∧
        m.e ∉ [s.a, s.b, s.c, s.d, s.e]) := by
  rcases hlegal.1 with ⟨⟨tau, htau, hleft⟩, ⟨rho, hrho, hright⟩⟩
  rcases m.legalIn_implies_endpoint_outside_move32_carrier
      s hrealized hlegal with hd | he
  · left
    refine ⟨tau, htau, ?_, ?_, ?_, ?_, hd⟩
    · exact (hleft m.a).2 (by simp [Move23Site.leftTet, Tet.verts])
    · exact (hleft m.b).2 (by simp [Move23Site.leftTet, Tet.verts])
    · exact (hleft m.c).2 (by simp [Move23Site.leftTet, Tet.verts])
    · exact (hleft m.d).2 (by simp [Move23Site.leftTet, Tet.verts])
  · right
    refine ⟨rho, hrho, ?_, ?_, ?_, ?_, he⟩
    · exact (hright m.a).2 (by simp [Move23Site.rightTet, Tet.verts])
    · exact (hright m.b).2 (by simp [Move23Site.rightTet, Tet.verts])
    · exact (hright m.c).2 (by simp [Move23Site.rightTet, Tet.verts])
    · exact (hright m.e).2 (by simp [Move23Site.rightTet, Tet.verts])

/-- In the no-degree-four branch, a legal `2 → 3` move whose shared face is
the represented source face of a realized `3 → 2` site must escape that
five-label carrier at both new-edge endpoints. -/
theorem Move23Site.both_endpoints_outside_move32_carrier_of_sourceFace_of_no_degree_four
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (hrealized : s.RealizedIn K)
    (ha : m.a = s.a)
    (hb : m.b = s.b)
    (hc : m.c = s.c)
    (hlegal : m.LegalIn K) :
    m.d ∉ [s.a, s.b, s.c, s.d, s.e] ∧
      m.e ∉ [s.a, s.b, s.c, s.d, s.e] := by
  rcases hlegal.1 with
    ⟨⟨tau, htau, hleft⟩, ⟨rho, hrho, hright⟩⟩

  have hsource0False :
      ∀ zeta : Tet,
        zeta ∈ K.tets →
        SameTetVertices zeta s.sourceTet₀ →
        False := by
    intro zeta hzeta hsame
    have hsupp : s.d ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨zeta, hzeta, (hsame s.d).2 (by
        simp [Move32Site.sourceTet₀, Tet.verts])⟩
    exact
      hcore.not_move32_sourceTet0_represented_of_no_degree_four_of_connectedLink
        hNoFour s hrealized ⟨zeta, hzeta, hsame⟩ (hlinks s.d hsupp)

  have hsource1False :
      ∀ zeta : Tet,
        zeta ∈ K.tets →
        SameTetVertices zeta s.sourceTet₁ →
        False := by
    intro zeta hzeta hsame
    have hsupp : s.e ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      simp only [allVerts, List.mem_flatMap]
      exact ⟨zeta, hzeta, (hsame s.e).2 (by
        simp [Move32Site.sourceTet₁, Tet.verts])⟩
    exact
      hcore.not_move32_sourceTet1_represented_of_no_degree_four_of_connectedLink
        hNoFour s hrealized ⟨zeta, hzeta, hsame⟩ (hlinks s.e hsupp)

  have hdD : m.d ≠ s.d := by
    intro h
    apply hsource0False tau htau
    simpa [Move23Site.leftTet, Move32Site.sourceTet₀,
      ha, hb, hc, h, Tet.verts] using hleft

  have hdE : m.d ≠ s.e := by
    intro h
    apply hsource1False tau htau
    simpa [Move23Site.leftTet, Move32Site.sourceTet₁,
      ha, hb, hc, h, Tet.verts] using hleft

  have heD : m.e ≠ s.d := by
    intro h
    apply hsource0False rho hrho
    simpa [Move23Site.rightTet, Move32Site.sourceTet₀,
      ha, hb, hc, h, Tet.verts] using hright

  have heE : m.e ≠ s.e := by
    intro h
    apply hsource1False rho hrho
    simpa [Move23Site.rightTet, Move32Site.sourceTet₁,
      ha, hb, hc, h, Tet.verts] using hright

  have hm := m.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  constructor
  · intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h <;> aesop
  · intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h | h <;> aesop

/-- If both endpoints of the escaping edge lie outside a realized Move32
carrier, the five carrier labels followed by those endpoints are seven
distinct labels. -/
theorem Move23Site.seven_labels_nodup_of_both_endpoints_outside_move32_carrier
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hrealized : s.RealizedIn K)
    (hd : m.d ∉ [s.a, s.b, s.c, s.d, s.e])
    (he : m.e ∉ [s.a, s.b, s.c, s.d, s.e]) :
    [s.a, s.b, s.c, s.d, s.e, m.d, m.e].Nodup := by
  have hs := hcore.move32Site_distinct s hrealized
  have hm := m.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false] at hs hm ⊢
  aesop

/-- The same no-degree-four source-face escape gives the seven labels in the
exact order required by `Move2332InitialEscapeSeed`, with `x = s.d` and
`y = s.e`. -/
theorem Move23Site.move2332_seven_labels_nodup_of_sourceFace_of_no_degree_four
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (hrealized : s.RealizedIn K)
    (ha : m.a = s.a)
    (hb : m.b = s.b)
    (hc : m.c = s.c)
    (hlegal : m.LegalIn K) :
    [m.a, m.b, m.c, m.d, m.e, s.d, s.e].Nodup := by
  rcases
      m.both_endpoints_outside_move32_carrier_of_sourceFace_of_no_degree_four
        s hcore hlinks hNoFour hrealized ha hb hc hlegal with
    ⟨hd, he⟩
  have hseven :=
    m.seven_labels_nodup_of_both_endpoints_outside_move32_carrier
      s hcore hrealized hd he
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false] at hseven ⊢
  aesop

/-- For a legal `2 → 3` site, incidence four of the original edge `(b,c)`
is exactly enough to leave two unchanged tetrahedra on that edge.  This is
the count required by the first `3 → 2` constructor in the move2332 seed. -/
theorem Move23Site.first_move2332_sharedEdge_count_two_of_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4 :
      (K.tets.filter (fun tau =>
        m.b ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4) :
    ((m.unchangedTets K).filter (fun tau =>
      m.b ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 2 := by
  let p : Tet → Prop := fun tau =>
    m.b ∈ tau.verts ∧ m.c ∈ tau.verts
  have hinvariant :
      ∀ tau sigma,
        SameTetVertices tau sigma →
        (p tau ↔ p sigma) := by
    intro tau sigma hsame
    constructor
    · intro h
      exact ⟨(hsame m.b).1 h.1, (hsame m.c).1 h.2⟩
    · intro h
      exact ⟨(hsame m.b).2 h.1, (hsame m.c).2 h.2⟩
  have hsplit :=
    hcore.move23Site_unchanged_filter_length_add_local_eq
      m hlegal p hinvariant
  have hlocal :
      ([m.leftTet, m.rightTet].filter p).length = 2 := by
    simp [p, Move23Site.leftTet, Move23Site.rightTet, Tet.verts]
  dsimp [p] at hsplit
  rw [hlocal] at hsplit
  omega

/-- Incidence four on the original `(b,c)` edge becomes incidence exactly
three after the legal `2 → 3`: the two unchanged edge tetrahedra survive and
only `newTet₂` among the three inserted tetrahedra contains both endpoints. -/
theorem Move23Site.replace_bc_edgeIncidence_three_of_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4 :
      (K.tets.filter (fun tau =>
        m.b ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4) :
    ((m.replace K).tets.filter (fun tau =>
      m.b ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 3 := by
  have htwo :=
    m.first_move2332_sharedEdge_count_two_of_incidence_four
      hcore hlegal hinc4
  rw [m.replace_tets_eq K]
  have hd := m.distinct
  simp at hd
  simpa [List.filter_cons, Move23Site.newTet₀, Move23Site.newTet₁,
    Move23Site.newTet₂, Tet.verts, hd, Ne.symm] using congrArg Nat.succ htwo

/-- Incidence four on the original `(b,c)` edge therefore produces a realized
exact-three Move32 candidate on that same edge after the legal `2 → 3`.
This does not assert source-face absence or Move32 legality. -/
theorem Move23Site.exists_first_move32_candidate_of_bc_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4 :
      (K.tets.filter (fun tau =>
        m.b ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4) :
    ∃ s₁ : Move32Site,
      s₁.d = m.b ∧
      s₁.e = m.c ∧
      s₁.RealizedIn (m.replace K) ∧
      s₁.SharedEdgeExactlyThree (m.replace K) := by
  have hcore' : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hthree :=
    m.replace_bc_edgeIncidence_three_of_incidence_four hcore hlegal hinc4
  have hbc : m.b ≠ m.c := by
    have hd := m.distinct
    simp at hd
    aesop
  exact
    hcore'.exists_move32Site_realizedIn_of_edgeIncidence_three
      m.b m.c hbc hthree

/-- If the `2 → 3` source face is aligned with a realized Move32 source face,
the old `targetTet₂` survives both source-tetrahedron erasures. -/
theorem Move23Site.exists_old_targetTet₂_in_unchanged_of_sourceFace_alignment
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hrealized : s.RealizedIn K)
    (ha : m.a = s.a) :
    ∃ tau ∈ m.unchangedTets K,
      SameTetVertices tau s.targetTet₂ := by
  obtain ⟨tau, htauK, hsame⟩ := hrealized.2.2
  have hfive := hcore.move32Site_distinct s hrealized
  have hsaNot : s.a ∉ s.targetTet₂.verts := by
    simp [Move32Site.targetTet₂, Tet.verts]
    simp at hfive
    aesop
  have hnotLeft : ¬ SameTetVertices tau m.leftTet := by
    intro hleft
    have hmaTau : m.a ∈ tau.verts :=
      (hleft m.a).2 (by simp [Move23Site.leftTet, Tet.verts])
    have hsaTau : s.a ∈ tau.verts := by
      simpa [ha] using hmaTau
    exact hsaNot ((hsame s.a).1 hsaTau)
  have hnotRight : ¬ SameTetVertices tau m.rightTet := by
    intro hright
    have hmaTau : m.a ∈ tau.verts :=
      (hright m.a).2 (by simp [Move23Site.rightTet, Tet.verts])
    have hsaTau : s.a ∈ tau.verts := by
      simpa [ha] using hmaTau
    exact hsaNot ((hsame s.a).1 hsaTau)
  have hafterLeft :
      tau ∈ eraseFirstSameTet m.leftTet K.tets :=
    mem_eraseFirstSameTet_of_mem_of_not_same htauK hnotLeft
  have hunchanged :
      tau ∈ eraseFirstSameTet m.rightTet
        (eraseFirstSameTet m.leftTet K.tets) :=
    mem_eraseFirstSameTet_of_mem_of_not_same hafterLeft hnotRight
  exact ⟨tau, by simpa [Move23Site.unchangedTets] using hunchanged, hsame⟩

/-- The represented `targetTet₂` has a distinct closed-core partner across
each of its two faces containing the source edge `(b,c)`. -/
theorem Move32Site.exists_targetTet₂_bc_face_partners
    {K : Triangulation} (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hrealized : s.RealizedIn K) :
    ∃ tau rhoD rhoE,
      tau ∈ K.tets ∧
      SameTetVertices tau s.targetTet₂ ∧
      rhoD ∈ K.tets ∧
      ¬ SameTetVertices tau rhoD ∧
      s.b ∈ rhoD.verts ∧
      s.c ∈ rhoD.verts ∧
      s.d ∈ rhoD.verts ∧
      rhoE ∈ K.tets ∧
      ¬ SameTetVertices tau rhoE ∧
      s.b ∈ rhoE.verts ∧
      s.c ∈ rhoE.verts ∧
      s.e ∈ rhoE.verts := by
  obtain ⟨tau, htauK, hsame⟩ := hrealized.2.2
  have hfive := hcore.move32Site_distinct s hrealized
  have hbTau : s.b ∈ tau.verts :=
    (hsame s.b).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  have hcTau : s.c ∈ tau.verts :=
    (hsame s.c).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  have hdTau : s.d ∈ tau.verts :=
    (hsame s.d).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  have heTau : s.e ∈ tau.verts :=
    (hsame s.e).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  have hbcd : [s.b, s.c, s.d].Nodup := by
    have h := hfive
    simp at h ⊢
    aesop
  have hbce : [s.b, s.c, s.e].Nodup := by
    have h := hfive
    simp at h ⊢
    aesop
  obtain ⟨rhoD, hrhoDK, hnotD, hbD, hcD, hdD⟩ :=
    hcore.exists_other_tet_across_triangle hbcd htauK hbTau hcTau hdTau
  obtain ⟨rhoE, hrhoEK, hnotE, hbE, hcE, heE⟩ :=
    hcore.exists_other_tet_across_triangle hbce htauK hbTau hcTau heTau
  exact
    ⟨tau, rhoD, rhoE, htauK, hsame,
      hrhoDK, hnotD, hbD, hcD, hdD,
      hrhoEK, hnotE, hbE, hcE, heE⟩

end Poincare
