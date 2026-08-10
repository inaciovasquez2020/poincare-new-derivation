import Poincare.OppositeFaceCommonComplement

namespace Poincare

private theorem incident_star_exhausted_of_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    {v : Nat} {a b c d : Tet}
    (haK : a ∈ K.tets) (hbK : b ∈ K.tets)
    (hcK : c ∈ K.tets) (hdK : d ∈ K.tets)
    (hva : v ∈ a.verts) (hvb : v ∈ b.verts)
    (hvc : v ∈ c.verts) (hvd : v ∈ d.verts)
    (hfour : [a, b, c, d].Nodup) :
    ∀ σ ∈ K.tets, v ∈ σ.verts →
      σ = a ∨ σ = b ∨ σ = c ∨ σ = d := by
  classical
  let incident := K.tets.filter (fun σ => v ∈ σ.verts)
  have hvSupport : v ∈ vertexSupport K := by
    apply (mem_vertexSupport_iff K v).2
    apply List.mem_flatMap.mpr
    exact ⟨a, haK, hva⟩
  have hincLength : incident.length = 4 := by
    exact hcore.incidentTetCount_eq_four_of_PhiSupport_eq_zero hPhi hvSupport
  have hincNodup : incident.Nodup := by
    apply List.Nodup.filter
    exact hcore.2.1.imp (by
      intro σ ρ hne hEq
      apply hne
      subst ρ
      intro x
      rfl)
  have hma : a ∈ incident := by simp [incident, haK, hva]
  have hmb : b ∈ incident := by simp [incident, hbK, hvb]
  have hmc : c ∈ incident := by simp [incident, hcK, hvc]
  have hmd : d ∈ incident := by simp [incident, hdK, hvd]
  intro σ hσK hvσ
  have hmσ : σ ∈ incident := by simp [incident, hσK, hvσ]
  by_contra hcases
  push Not at hcases
  have hfive : [a, b, c, d, σ].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or,
      List.nodup_nil, and_true]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hfour
    aesop
  have hsub : [a, b, c, d, σ].toFinset ⊆ incident.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at hx ⊢
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hma
    · exact hmb
    · exact hmc
    · exact hmd
    · exact hmσ
  have hcard := Finset.card_le_card hsub
  have hleft : [a, b, c, d, σ].toFinset.card = 5 := by
    simpa using List.toFinset_card_of_nodup hfive
  have hright : incident.toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup hincNodup, hincLength]
  rw [hleft, hright] at hcard
  omega

/-- The five tetrahedra in the local boundary-of-a-4-simplex pattern exhaust
the incident star at each of their five vertices. -/
theorem ClosedTriangulationCore.exists_five_tet_cluster_star_saturation
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    {τ : Tet}
    (hτK : τ ∈ K.tets)
    (hτ : τ.verts.Nodup) :
    ∃ ρ012 ρ013 ρ023 ρ123 e,
      ρ012 ∈ K.tets ∧ ρ013 ∈ K.tets ∧ ρ023 ∈ K.tets ∧ ρ123 ∈ K.tets ∧
      e ∉ τ.verts ∧
      τ.v0 ∈ ρ012.verts ∧ τ.v1 ∈ ρ012.verts ∧ τ.v2 ∈ ρ012.verts ∧ e ∈ ρ012.verts ∧
      τ.v0 ∈ ρ013.verts ∧ τ.v1 ∈ ρ013.verts ∧ τ.v3 ∈ ρ013.verts ∧ e ∈ ρ013.verts ∧
      τ.v0 ∈ ρ023.verts ∧ τ.v2 ∈ ρ023.verts ∧ τ.v3 ∈ ρ023.verts ∧ e ∈ ρ023.verts ∧
      τ.v1 ∈ ρ123.verts ∧ τ.v2 ∈ ρ123.verts ∧ τ.v3 ∈ ρ123.verts ∧ e ∈ ρ123.verts ∧
      (∀ v ∈ ρ012.verts, v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v2 ∨ v = e) ∧
      (∀ v ∈ ρ013.verts, v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v3 ∨ v = e) ∧
      (∀ v ∈ ρ023.verts, v = τ.v0 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e) ∧
      (∀ v ∈ ρ123.verts, v = τ.v1 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e) ∧
      (∀ σ ∈ K.tets, τ.v0 ∈ σ.verts → σ = τ ∨ σ = ρ012 ∨ σ = ρ013 ∨ σ = ρ023) ∧
      (∀ σ ∈ K.tets, τ.v1 ∈ σ.verts → σ = τ ∨ σ = ρ012 ∨ σ = ρ013 ∨ σ = ρ123) ∧
      (∀ σ ∈ K.tets, τ.v2 ∈ σ.verts → σ = τ ∨ σ = ρ012 ∨ σ = ρ023 ∨ σ = ρ123) ∧
      (∀ σ ∈ K.tets, τ.v3 ∈ σ.verts → σ = τ ∨ σ = ρ013 ∨ σ = ρ023 ∨ σ = ρ123) ∧
      (∀ σ ∈ K.tets, e ∈ σ.verts → σ = ρ012 ∨ σ = ρ013 ∨ σ = ρ023 ∨ σ = ρ123) := by
  classical
  obtain ⟨ρ012, ρ013, ρ023, ρ123, e,
    h012K, h013K, h023K, h123K, heτ,
    h0_012, h1_012, h2_012, h0_013, h1_013, h3_013,
    h0_023, h2_023, h3_023, he012, he013, he023, he123,
    h1_123, h2_123, h3_123, h012Cover, h013Cover, h023Cover, h123Cover⟩ :=
      hcore.exists_opposite_face_common_complement hPhi hτK hτ
  have hτ_012 : τ ≠ ρ012 := by intro h; subst ρ012; exact heτ he012
  have hτ_013 : τ ≠ ρ013 := by intro h; subst ρ013; exact heτ he013
  have hτ_023 : τ ≠ ρ023 := by intro h; subst ρ023; exact heτ he023
  have hτ_123 : τ ≠ ρ123 := by intro h; subst ρ123; exact heτ he123
  have h012_013 : ρ012 ≠ ρ013 := by
    intro h; subst ρ013
    rcases h013Cover τ.v2 h2_012 with h | h | h | h
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · exact heτ (h.symm ▸ by simp [Tet.verts])
  have h012_023 : ρ012 ≠ ρ023 := by
    intro h; subst ρ023
    rcases h023Cover τ.v1 h1_012 with h | h | h | h
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · exact heτ (h.symm ▸ by simp [Tet.verts])
  have h012_123 : ρ012 ≠ ρ123 := by
    intro h; subst ρ123
    rcases h123Cover τ.v0 h0_012 with h | h | h | h
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · exact heτ (h.symm ▸ by simp [Tet.verts])
  have h013_023 : ρ013 ≠ ρ023 := by
    intro h; subst ρ023
    rcases h023Cover τ.v1 h1_013 with h | h | h | h
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · exact heτ (h.symm ▸ by simp [Tet.verts])
  have h013_123 : ρ013 ≠ ρ123 := by
    intro h; subst ρ123
    rcases h123Cover τ.v0 h0_013 with h | h | h | h
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · exact heτ (h.symm ▸ by simp [Tet.verts])
  have h023_123 : ρ023 ≠ ρ123 := by
    intro h; subst ρ123
    rcases h123Cover τ.v0 h0_023 with h | h | h | h
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · exact heτ (h.symm ▸ by simp [Tet.verts])
  have hstar0 := incident_star_exhausted_of_four hcore hPhi hτK h012K h013K h023K
    (by simp [Tet.verts]) h0_012 h0_013 h0_023 (by simp; aesop)
  have hstar1 := incident_star_exhausted_of_four hcore hPhi hτK h012K h013K h123K
    (by simp [Tet.verts]) h1_012 h1_013 h1_123 (by simp; aesop)
  have hstar2 := incident_star_exhausted_of_four hcore hPhi hτK h012K h023K h123K
    (by simp [Tet.verts]) h2_012 h2_023 h2_123 (by simp; aesop)
  have hstar3 := incident_star_exhausted_of_four hcore hPhi hτK h013K h023K h123K
    (by simp [Tet.verts]) h3_013 h3_023 h3_123 (by simp; aesop)
  have hstare := incident_star_exhausted_of_four hcore hPhi h012K h013K h023K h123K
    he012 he013 he023 he123 (by simp; aesop)
  exact ⟨ρ012, ρ013, ρ023, ρ123, e,
    h012K, h013K, h023K, h123K, heτ,
    h0_012, h1_012, h2_012, he012,
    h0_013, h1_013, h3_013, he013,
    h0_023, h2_023, h3_023, he023,
    h1_123, h2_123, h3_123, he123,
    h012Cover, h013Cover, h023Cover, h123Cover,
    hstar0, hstar1, hstar2, hstar3, hstare⟩

end Poincare
