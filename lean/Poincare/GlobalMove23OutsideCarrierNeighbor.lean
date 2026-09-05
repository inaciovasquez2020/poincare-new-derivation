import Poincare.GlobalMove32CarrierPairRepresented
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
  have hd := m.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false] at hd
  rw [m.replace_tets_eq K]
  simp [Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂,
    Tet.verts, hd, htwo]

end Poincare
