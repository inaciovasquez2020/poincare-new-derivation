import Poincare.CommonNeighborComplement

namespace Poincare

/-- The face opposite the first vertex has the same complementary vertex as
the three face-neighbors through that vertex. -/
theorem ClosedTriangulationCore.exists_opposite_face_common_complement
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    {τ : Tet}
    (hτK : τ ∈ K.tets)
    (hτ : τ.verts.Nodup) :
    ∃ ρ012 ρ013 ρ023 ρ123 e,
      ρ012 ∈ K.tets ∧ ρ013 ∈ K.tets ∧ ρ023 ∈ K.tets ∧ ρ123 ∈ K.tets ∧
      e ∉ τ.verts ∧
      τ.v0 ∈ ρ012.verts ∧ τ.v1 ∈ ρ012.verts ∧ τ.v2 ∈ ρ012.verts ∧
      τ.v0 ∈ ρ013.verts ∧ τ.v1 ∈ ρ013.verts ∧ τ.v3 ∈ ρ013.verts ∧
      τ.v0 ∈ ρ023.verts ∧ τ.v2 ∈ ρ023.verts ∧ τ.v3 ∈ ρ023.verts ∧
      e ∈ ρ012.verts ∧ e ∈ ρ013.verts ∧ e ∈ ρ023.verts ∧ e ∈ ρ123.verts ∧
      τ.v1 ∈ ρ123.verts ∧ τ.v2 ∈ ρ123.verts ∧ τ.v3 ∈ ρ123.verts ∧
      (∀ v ∈ ρ012.verts,
        v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v2 ∨ v = e) ∧
      (∀ v ∈ ρ013.verts,
        v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v3 ∨ v = e) ∧
      (∀ v ∈ ρ023.verts,
        v = τ.v0 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e) ∧
      (∀ v ∈ ρ123.verts,
        v = τ.v1 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e) := by
  classical
  obtain ⟨ρ012, ρ013, ρ023, e,
    hρ012K, hρ013K, hρ023K, he0, he1, he2, he3, heτ,
    h0_012, h1_012, h2_012, h0_013, h1_013, h3_013,
    h0_023, h2_023, h3_023, he012, he013, he023,
    h012Cover, h013Cover, h023Cover⟩ :=
      hcore.exists_common_v0_neighbor_complement hPhi hτK hτ
  have h12e : [τ.v1, τ.v2, e].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true]
    simp [Tet.verts] at hτ
    aesop
  obtain ⟨σ12e, hσK, hnσ, h1σ, h2σ, heσ⟩ :=
    hcore.exists_other_tet_across_triangle h12e hρ012K h1_012 h2_012 he012
  have hτ_012 : τ ≠ ρ012 := by
    intro h
    subst ρ012
    exact heτ he012
  have hτ_013 : τ ≠ ρ013 := by
    intro h
    subst ρ013
    exact heτ he013
  have hτ_σ : τ ≠ σ12e := by
    intro h
    subst σ12e
    exact heτ heσ
  have h012_013 : ρ012 ≠ ρ013 := by
    intro h
    subst ρ013
    rcases h013Cover τ.v2 h2_012 with h | h | h | h
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · exact he2 h.symm
  have h012_σ : ρ012 ≠ σ12e := by
    intro h
    apply hnσ
    subst σ12e
    intro v
    rfl
  have h013_σ : ρ013 ≠ σ12e := by
    intro h
    subst σ12e
    rcases h013Cover τ.v2 h2σ with h | h | h | h
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · simp [Tet.verts] at hτ; aesop
    · exact he2 h.symm
  let incident := K.tets.filter (fun σ => τ.v1 ∈ σ.verts)
  have hincLength : incident.length = 4 := by
    apply hcore.incidentTetCount_eq_four_of_PhiSupport_eq_zero hPhi
    apply (mem_vertexSupport_iff K τ.v1).2
    apply List.mem_flatMap.mpr
    exact ⟨τ, hτK, by simp [Tet.verts]⟩
  have hincNodup : incident.Nodup := by
    apply List.Nodup.filter
    exact hcore.2.1.imp (by
      intro σ ρ hne hEq
      apply hne
      subst ρ
      intro v
      rfl)
  have hmemτ : τ ∈ incident := by simp [incident, hτK, Tet.verts]
  have hmem012 : ρ012 ∈ incident := by simp [incident, hρ012K, h1_012]
  have hmem013 : ρ013 ∈ incident := by simp [incident, hρ013K, h1_013]
  have hmemσ : σ12e ∈ incident := by simp [incident, hσK, h1σ]
  have hstar : ∀ σ ∈ K.tets, τ.v1 ∈ σ.verts →
      σ = τ ∨ σ = ρ012 ∨ σ = ρ013 ∨ σ = σ12e := by
    intro σ hσK' h1σ'
    have hmemσ' : σ ∈ incident := by simp [incident, hσK', h1σ']
    by_contra hcases
    push Not at hcases
    have hfive : [τ, ρ012, ρ013, σ12e, σ].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, not_or,
        List.nodup_nil, and_true]
      aesop
    have hsub : [τ, ρ012, ρ013, σ12e, σ].toFinset ⊆ incident.toFinset := by
      intro x hx
      simp only [List.mem_toFinset] at hx ⊢
      simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hmemτ
      · exact hmem012
      · exact hmem013
      · exact hmemσ
      · exact hmemσ'
    have hcard := Finset.card_le_card hsub
    have hleft : [τ, ρ012, ρ013, σ12e, σ].toFinset.card = 5 := by
      simpa using List.toFinset_card_of_nodup hfive
    have hright : incident.toFinset.card = 4 := by
      rw [List.toFinset_card_of_nodup hincNodup, hincLength]
    rw [hleft, hright] at hcard
    omega
  have h123 : [τ.v1, τ.v2, τ.v3].Nodup := by
    simp [Tet.verts] at hτ ⊢
    aesop
  obtain ⟨ρ123, hρ123K, hn123, h1_123, h2_123, h3_123⟩ :=
    hcore.exists_other_tet_across_triangle h123 hτK
      (by simp [Tet.verts]) (by simp [Tet.verts]) (by simp [Tet.verts])
  have hρ123eq : ρ123 = σ12e := by
    rcases hstar ρ123 hρ123K h1_123 with h | h | h | h
    · subst ρ123
      exact False.elim (hn123 (fun _ => Iff.rfl))
    · subst ρ123
      rcases h012Cover τ.v3 h3_123 with q | q | q | q
      · simp [Tet.verts] at hτ; aesop
      · simp [Tet.verts] at hτ; aesop
      · simp [Tet.verts] at hτ; aesop
      · exact False.elim (he3 q.symm)
    · subst ρ123
      rcases h013Cover τ.v2 h2_123 with q | q | q | q
      · simp [Tet.verts] at hτ; aesop
      · simp [Tet.verts] at hτ; aesop
      · simp [Tet.verts] at hτ; aesop
      · exact False.elim (he2 q.symm)
    · exact h
  have he123 : e ∈ ρ123.verts := hρ123eq ▸ heσ
  have hρ123 := hcore.1 ρ123 hρ123K
  obtain ⟨f, hfdata, hfunique⟩ :=
    ρ123.exists_unique_complement_vertex hρ123 h123 h1_123 h2_123 h3_123
  have hfe : f = e := (hfunique e ⟨he123, he1, he2, he3⟩).symm
  have h123Cover : ∀ v ∈ ρ123.verts,
      v = τ.v1 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e := by
    intro v hv
    by_cases hface : v ∈ [τ.v1, τ.v2, τ.v3]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hface
      rcases hface with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · right; right; right
      have hv1 : v ≠ τ.v1 := by intro h; apply hface; simp [h]
      have hv2 : v ≠ τ.v2 := by intro h; apply hface; simp [h]
      have hv3 : v ≠ τ.v3 := by intro h; apply hface; simp [h]
      exact (hfunique v ⟨hv, hv1, hv2, hv3⟩).trans hfe
  exact ⟨ρ012, ρ013, ρ023, ρ123, e,
    hρ012K, hρ013K, hρ023K, hρ123K, heτ,
    h0_012, h1_012, h2_012, h0_013, h1_013, h3_013,
    h0_023, h2_023, h3_023,
    he012, he013, he023, he123, h1_123, h2_123, h3_123,
    h012Cover, h013Cover, h023Cover, h123Cover⟩

end Poincare
