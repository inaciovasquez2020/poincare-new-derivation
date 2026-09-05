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

end Poincare
