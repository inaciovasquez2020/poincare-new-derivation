import Poincare.GlobalMove23OutsideCarrierNeighbor

namespace Poincare

/-- Two closed-core partner tetrahedra across the `(b,c,d)` and `(b,c,e)`
faces of the same represented `targetTet₂` are distinct. -/
theorem Move32Site.targetTet₂_bc_face_partners_ne
    {K : Triangulation} (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hrealized : s.RealizedIn K)
    {tau rhoD rhoE : Tet}
    (hsame : SameTetVertices tau s.targetTet₂)
    (hrhoDK : rhoD ∈ K.tets)
    (hnotD : ¬ SameTetVertices tau rhoD)
    (hbD : s.b ∈ rhoD.verts)
    (hcD : s.c ∈ rhoD.verts)
    (hdD : s.d ∈ rhoD.verts)
    (heE : s.e ∈ rhoE.verts) :
    rhoD ≠ rhoE := by
  intro heq
  subst rhoE
  have hnodup : rhoD.verts.Nodup := hcore.1 rhoD hrhoDK
  have hfive := hcore.move32Site_distinct s hrealized
  have htargetNodup : [s.b, s.c, s.d, s.e].Nodup := by
    have h := hfive
    simp at h ⊢
    aesop
  have hsub :
      [s.b, s.c, s.d, s.e].toFinset ⊆ rhoD.verts.toFinset := by
    intro v hv
    simp only [List.mem_toFinset] at hv ⊢
    simp only [List.mem_cons, List.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hbD
    · exact hcD
    · exact hdD
    · exact heE
  have hcardTarget : [s.b, s.c, s.d, s.e].toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup htargetNodup]
    rfl
  have hcardRho : rhoD.verts.toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup hnodup]
    simp [Tet.verts]
  have heqFin :
      [s.b, s.c, s.d, s.e].toFinset = rhoD.verts.toFinset := by
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  have hsameDT : SameTetVertices rhoD s.targetTet₂ := by
    intro v
    change v ∈ rhoD.verts ↔ v ∈ [s.b, s.c, s.d, s.e]
    simpa only [List.mem_toFinset] using
      (show v ∈ rhoD.verts.toFinset ↔
          v ∈ [s.b, s.c, s.d, s.e].toFinset by
        rw [heqFin])
  have hsameTauD : SameTetVertices tau rhoD := by
    intro v
    constructor
    · intro hv
      exact (hsameDT v).2 ((hsame v).1 hv)
    · intro hv
      exact (hsame v).2 ((hsameDT v).1 hv)
  exact hnotD hsameTauD

/-- Under source-face alignment in the no-degree-four branch, the closed-core
partner across `(b,c,d)` cannot be either of the two legal Move23 source
tetrahedra. -/
theorem Move23Site.targetTet₂_bc_d_partner_not_move23_sources_of_sourceFace_alignment
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (hrealized : s.RealizedIn K)
    (ha : m.a = s.a)
    (hb : m.b = s.b)
    (hc : m.c = s.c)
    (hlegal : m.LegalIn K)
    {rhoD : Tet}
    (hdD : s.d ∈ rhoD.verts) :
    ¬ SameTetVertices rhoD m.leftTet ∧
      ¬ SameTetVertices rhoD m.rightTet := by
  obtain ⟨hmdOutside, hmeOutside⟩ :=
    m.both_endpoints_outside_move32_carrier_of_sourceFace_of_no_degree_four
      s hcore hlinks hNoFour hrealized ha hb hc hlegal
  have hfive := hcore.move32Site_distinct s hrealized
  have hsdNotLeft : s.d ∉ m.leftTet.verts := by
    have h := hfive
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmdOutside
    simp [Move23Site.leftTet, Tet.verts, ha, hb, hc]
    aesop
  have hsdNotRight : s.d ∉ m.rightTet.verts := by
    have h := hfive
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmeOutside
    simp [Move23Site.rightTet, Tet.verts, ha, hb, hc]
    aesop
  constructor
  · intro hsame
    exact hsdNotLeft ((hsame s.d).1 hdD)
  · intro hsame
    exact hsdNotRight ((hsame s.d).1 hdD)

/-- Under the same source-face alignment, the closed-core partner across
`(b,c,e)` cannot be either legal Move23 source tetrahedron. -/
theorem Move23Site.targetTet₂_bc_e_partner_not_move23_sources_of_sourceFace_alignment
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (hrealized : s.RealizedIn K)
    (ha : m.a = s.a)
    (hb : m.b = s.b)
    (hc : m.c = s.c)
    (hlegal : m.LegalIn K)
    {rhoE : Tet}
    (heE : s.e ∈ rhoE.verts) :
    ¬ SameTetVertices rhoE m.leftTet ∧
      ¬ SameTetVertices rhoE m.rightTet := by
  obtain ⟨hmdOutside, hmeOutside⟩ :=
    m.both_endpoints_outside_move32_carrier_of_sourceFace_of_no_degree_four
      s hcore hlinks hNoFour hrealized ha hb hc hlegal
  have hfive := hcore.move32Site_distinct s hrealized
  have hseNotLeft : s.e ∉ m.leftTet.verts := by
    have h := hfive
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmdOutside
    simp [Move23Site.leftTet, Tet.verts, ha, hb, hc]
    aesop
  have hseNotRight : s.e ∉ m.rightTet.verts := by
    have h := hfive
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmeOutside
    simp [Move23Site.rightTet, Tet.verts, ha, hb, hc]
    aesop
  constructor
  · intro hsame
    exact hseNotLeft ((hsame s.e).1 heE)
  · intro hsame
    exact hseNotRight ((hsame s.e).1 heE)

end Poincare
