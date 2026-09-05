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
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
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

/-- Any represented `targetTet₂` survives the two Move23 source erasures when
the Move23 source face is aligned with the Move32 source face. -/
theorem Move23Site.targetTet₂_representative_mem_unchanged_of_sourceFace_alignment
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hrealized : s.RealizedIn K)
    (ha : m.a = s.a)
    {tau : Tet}
    (htauK : tau ∈ K.tets)
    (hsame : SameTetVertices tau s.targetTet₂) :
    tau ∈ m.unchangedTets K := by
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
  simpa [Move23Site.unchangedTets] using hunchanged

/-- A legal Move23 whose source face is the source face of a realized Move32
site cannot be an incidence-four escape on `(b,c)`.  In the no-degree-four
branch the represented `targetTet₂` and its two distinct closed-face partners
all survive the Move23 source erasures, so three unchanged tetrahedra already
contain `(b,c)`; adding the two Move23 source tetrahedra forces incidence at
least five. -/
theorem Move23Site.five_le_bc_edgeIncidence_of_sourceFace_alignment_of_no_degree_four
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (hrealized : s.RealizedIn K)
    (ha : m.a = s.a)
    (hb : m.b = s.b)
    (hc : m.c = s.c)
    (hlegal : m.LegalIn K) :
    5 ≤ (K.tets.filter (fun tau =>
      m.b ∈ tau.verts ∧ m.c ∈ tau.verts)).length := by
  classical
  obtain ⟨tau, rhoD, rhoE,
      htauK, hsame,
      hrhoDK, hnotD, hbD, hcD, hdD,
      hrhoEK, hnotE, hbE, hcE, heE⟩ :=
    s.exists_targetTet₂_bc_face_partners hcore hrealized
  have htauUnchanged : tau ∈ m.unchangedTets K :=
    m.targetTet₂_representative_mem_unchanged_of_sourceFace_alignment
      s hcore hrealized ha htauK hsame
  obtain ⟨hDleft, hDright⟩ :=
    m.targetTet₂_bc_d_partner_not_move23_sources_of_sourceFace_alignment
      s hcore hlinks hNoFour hrealized ha hb hc hlegal hdD
  obtain ⟨hEleft, hEright⟩ :=
    m.targetTet₂_bc_e_partner_not_move23_sources_of_sourceFace_alignment
      s hcore hlinks hNoFour hrealized ha hb hc hlegal heE
  have hDAfterLeft :
      rhoD ∈ eraseFirstSameTet m.leftTet K.tets :=
    mem_eraseFirstSameTet_of_mem_of_not_same hrhoDK hDleft
  have hDUnchanged : rhoD ∈ m.unchangedTets K := by
    have h := mem_eraseFirstSameTet_of_mem_of_not_same hDAfterLeft hDright
    simpa [Move23Site.unchangedTets] using h
  have hEAfterLeft :
      rhoE ∈ eraseFirstSameTet m.leftTet K.tets :=
    mem_eraseFirstSameTet_of_mem_of_not_same hrhoEK hEleft
  have hEUnchanged : rhoE ∈ m.unchangedTets K := by
    have h := mem_eraseFirstSameTet_of_mem_of_not_same hEAfterLeft hEright
    simpa [Move23Site.unchangedTets] using h
  have hbTau : m.b ∈ tau.verts := by
    rw [hb]
    exact (hsame s.b).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  have hcTau : m.c ∈ tau.verts := by
    rw [hc]
    exact (hsame s.c).2 (by simp [Move32Site.targetTet₂, Tet.verts])
  have hbD' : m.b ∈ rhoD.verts := by simpa [hb] using hbD
  have hcD' : m.c ∈ rhoD.verts := by simpa [hc] using hcD
  have hbE' : m.b ∈ rhoE.verts := by simpa [hb] using hbE
  have hcE' : m.c ∈ rhoE.verts := by simpa [hc] using hcE
  let U := (m.unchangedTets K).filter (fun zeta =>
    m.b ∈ zeta.verts ∧ m.c ∈ zeta.verts)
  have htauU : tau ∈ U := by
    simp [U, htauUnchanged, hbTau, hcTau]
  have hDU : rhoD ∈ U := by
    simp [U, hDUnchanged, hbD', hcD']
  have hEU : rhoE ∈ U := by
    simp [U, hEUnchanged, hbE', hcE']
  have htauD : tau ≠ rhoD := by
    intro heq
    subst rhoD
    exact hnotD (sameTetVertices_refl tau)
  have htauE : tau ≠ rhoE := by
    intro heq
    subst rhoE
    exact hnotE (sameTetVertices_refl tau)
  have hDE : rhoD ≠ rhoE :=
    s.targetTet₂_bc_face_partners_ne hcore hrealized hsame
      hrhoDK hnotD hbD hcD hdD heE
  let W : Finset Tet := {tau, rhoD, rhoE}
  have hWcard : W.card = 3 := by
    simp [W, htauD, htauE, hDE, Ne.symm]
  have hWsub : W ⊆ U.toFinset := by
    intro z hz
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact List.mem_toFinset.mpr htauU
    · exact List.mem_toFinset.mpr hDU
    · exact List.mem_toFinset.mpr hEU
  have hUthree : 3 ≤ U.length := by
    have hcardle : W.card ≤ U.toFinset.card := Finset.card_le_card hWsub
    have htoFinset : U.toFinset.card ≤ U.length := List.toFinset_card_le U
    rw [hWcard] at hcardle
    omega
  let p : Tet → Prop := fun zeta =>
    m.b ∈ zeta.verts ∧ m.c ∈ zeta.verts
  have hinvariant :
      ∀ zeta theta,
        SameTetVertices zeta theta →
        (p zeta ↔ p theta) := by
    intro zeta theta hsameZT
    constructor
    · intro h
      exact ⟨(hsameZT m.b).1 h.1, (hsameZT m.c).1 h.2⟩
    · intro h
      exact ⟨(hsameZT m.b).2 h.1, (hsameZT m.c).2 h.2⟩
  have hsplit :=
    hcore.move23Site_unchanged_filter_length_add_local_eq
      m hlegal p hinvariant
  have hlocal : ([m.leftTet, m.rightTet].filter p).length = 2 := by
    simp [p, Move23Site.leftTet, Move23Site.rightTet, Tet.verts]
  rw [hlocal] at hsplit
  dsimp [p] at hsplit
  dsimp [U] at hUthree
  omega

end Poincare