import Poincare.VertexStarSaturation

namespace Poincare

/-- The three face-neighbors through the first vertex of a nondegenerate
tetrahedron share one complementary vertex. -/
theorem ClosedTriangulationCore.exists_common_v0_neighbor_complement
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    {τ : Tet}
    (hτK : τ ∈ K.tets)
    (hτ : τ.verts.Nodup) :
    ∃ ρ012 ρ013 ρ023 e,
      ρ012 ∈ K.tets ∧ ρ013 ∈ K.tets ∧ ρ023 ∈ K.tets ∧
      e ≠ τ.v0 ∧ e ≠ τ.v1 ∧ e ≠ τ.v2 ∧ e ≠ τ.v3 ∧
      e ∉ τ.verts ∧
      τ.v0 ∈ ρ012.verts ∧ τ.v1 ∈ ρ012.verts ∧ τ.v2 ∈ ρ012.verts ∧
      τ.v0 ∈ ρ013.verts ∧ τ.v1 ∈ ρ013.verts ∧ τ.v3 ∈ ρ013.verts ∧
      τ.v0 ∈ ρ023.verts ∧ τ.v2 ∈ ρ023.verts ∧ τ.v3 ∈ ρ023.verts ∧
      e ∈ ρ012.verts ∧ e ∈ ρ013.verts ∧ e ∈ ρ023.verts ∧
      (∀ v ∈ ρ012.verts,
        v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v2 ∨ v = e) ∧
      (∀ v ∈ ρ013.verts,
        v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v3 ∨ v = e) ∧
      (∀ v ∈ ρ023.verts,
        v = τ.v0 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e) := by
  classical
  have h012 : [τ.v0, τ.v1, τ.v2].Nodup := by
    simp [Tet.verts] at hτ ⊢
    aesop
  have h013 : [τ.v0, τ.v1, τ.v3].Nodup := by
    simp [Tet.verts] at hτ ⊢
    aesop
  have h023 : [τ.v0, τ.v2, τ.v3].Nodup := by
    simp [Tet.verts] at hτ ⊢
    aesop
  have h01e (e : Nat) (he0 : e ≠ τ.v0) (he1 : e ≠ τ.v1) :
      [τ.v0, τ.v1, e].Nodup := by
    have h := h012
    simp at h ⊢
    aesop
  have h02e (e : Nat) (he0 : e ≠ τ.v0) (he2 : e ≠ τ.v2) :
      [τ.v0, τ.v2, e].Nodup := by
    have h := h012
    simp at h ⊢
    aesop
  obtain ⟨ρ012, ρ013, ρ023,
    hρ012K, hρ013K, hρ023K,
    h0_012, h1_012, h2_012,
    h0_013, h1_013, h3_013,
    h0_023, h2_023, h3_023,
    hn012, hn013, hn023,
    hτ012, hτ013, hτ023, h012013, h012023, h013023, hstar⟩ :=
      hcore.exists_vertex_star_saturation hPhi hτK hτ
  have hρ012 := hcore.1 ρ012 hρ012K
  have hρ013 := hcore.1 ρ013 hρ013K
  have hρ023 := hcore.1 ρ023 hρ023K
  obtain ⟨d, e, hdτ, hdabc, he012, heabc, hde, hτCover, h012Cover⟩ :=
    Tet.exists_distinct_complement_vertices τ ρ012 hτ hρ012 h012
      (by simp [Tet.verts]) (by simp [Tet.verts]) (by simp [Tet.verts])
      h0_012 h1_012 h2_012 hn012
  have hd3 : d = τ.v3 := by
    rcases hτCover τ.v3 (by simp [Tet.verts]) with h | h | h | h
    · simp [Tet.verts] at hτ
      aesop
    · simp [Tet.verts] at hτ
      aesop
    · simp [Tet.verts] at hτ
      aesop
    · exact h.symm
  have he0 : e ≠ τ.v0 := by
    intro h
    apply heabc
    simp [h]
  have he1 : e ≠ τ.v1 := by
    intro h
    apply heabc
    simp [h]
  have he2 : e ≠ τ.v2 := by
    intro h
    apply heabc
    simp [h]
  have he3 : e ≠ τ.v3 := by simpa [hd3] using hde.symm
  have heτ : e ∉ τ.verts := by simp [Tet.verts, he0, he1, he2, he3]

  have h1not023 : τ.v1 ∉ ρ023.verts := by
    obtain ⟨d', f, hd'τ, hd'face, hf023, hfface, hd'f,
      hτCover', h023Cover⟩ :=
      Tet.exists_distinct_complement_vertices τ ρ023 hτ hρ023 h023
        (by simp [Tet.verts]) (by simp [Tet.verts]) (by simp [Tet.verts])
        h0_023 h2_023 h3_023 hn023
    intro h1
    rcases h023Cover τ.v1 h1 with h | h | h | h
    · simp [Tet.verts] at hτ
      aesop
    · simp [Tet.verts] at hτ
      aesop
    · simp [Tet.verts] at hτ
      aesop
    · have hd'1 : d' = τ.v1 := by
        rcases hτCover' τ.v1 (by simp [Tet.verts]) with q | q | q | q
        · simp [Tet.verts] at hτ
          aesop
        · simp [Tet.verts] at hτ
          aesop
        · simp [Tet.verts] at hτ
          aesop
        · exact q.symm
      exact hd'f (hd'1.trans h)

  obtain ⟨σ, hσK, hnσ, h0σ, h1σ, heσ⟩ :=
    hcore.exists_other_tet_across_triangle (h01e e he0 he1) hρ012K
      h0_012 h1_012 he012
  have hσeq : σ = ρ013 := by
    rcases hstar σ hσK h0σ with rfl | h | h | h
    · exact False.elim (heτ heσ)
    · exact False.elim (hnσ (by simpa [h] using (show SameTetVertices ρ012 ρ012 from fun _ => Iff.rfl)))
    · exact h
    · exact False.elim (h1not023 (h ▸ h1σ))
  have he013 : e ∈ ρ013.verts := hσeq ▸ heσ

  have h2not013 : τ.v2 ∉ ρ013.verts := by
    obtain ⟨d', f, hd'τ, hd'face, hf013, hfface, hd'f,
      hτCover', h013Cover⟩ :=
      Tet.exists_distinct_complement_vertices τ ρ013 hτ hρ013 h013
        (by simp [Tet.verts]) (by simp [Tet.verts]) (by simp [Tet.verts])
        h0_013 h1_013 h3_013 hn013
    intro h2
    rcases h013Cover τ.v2 h2 with h | h | h | h
    · simp [Tet.verts] at hτ
      aesop
    · simp [Tet.verts] at hτ
      aesop
    · simp [Tet.verts] at hτ
      aesop
    · have hd'2 : d' = τ.v2 := by
        rcases hτCover' τ.v2 (by simp [Tet.verts]) with q | q | q | q
        · simp [Tet.verts] at hτ
          aesop
        · simp [Tet.verts] at hτ
          aesop
        · simp [Tet.verts] at hτ
          aesop
        · exact q.symm
      exact hd'f (hd'2.trans h)

  obtain ⟨σ', hσ'K, hnσ', h0σ', h2σ', heσ'⟩ :=
    hcore.exists_other_tet_across_triangle (h02e e he0 he2) hρ012K
      h0_012 h2_012 he012
  have hσ'eq : σ' = ρ023 := by
    rcases hstar σ' hσ'K h0σ' with rfl | h | h | h
    · exact False.elim (heτ heσ')
    · exact False.elim (hnσ' (by simpa [h] using (show SameTetVertices ρ012 ρ012 from fun _ => Iff.rfl)))
    · exact False.elim (h2not013 (h ▸ h2σ'))
    · exact h
  have he023 : e ∈ ρ023.verts := hσ'eq ▸ heσ'

  obtain ⟨e013, he013data, he013unique⟩ :=
    ρ013.exists_unique_complement_vertex hρ013
      h013 h0_013 h1_013 h3_013
  have he013eq : e013 = e := (he013unique e ⟨he013, he0, he1, he3⟩).symm
  have h013Cover : ∀ v ∈ ρ013.verts,
      v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v3 ∨ v = e := by
    intro v hv
    by_cases hface : v ∈ [τ.v0, τ.v1, τ.v3]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hface
      rcases hface with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · right; right; right
      have hv0 : v ≠ τ.v0 := by
        intro h; apply hface; simp [h]
      have hv1 : v ≠ τ.v1 := by
        intro h; apply hface; simp [h]
      have hv3 : v ≠ τ.v3 := by
        intro h; apply hface; simp [h]
      exact (he013unique v ⟨hv, hv0, hv1, hv3⟩).trans he013eq
  obtain ⟨e023, he023data, he023unique⟩ :=
    ρ023.exists_unique_complement_vertex hρ023
      h023 h0_023 h2_023 h3_023
  have he023eq : e023 = e := (he023unique e ⟨he023, he0, he2, he3⟩).symm
  have h023Cover : ∀ v ∈ ρ023.verts,
      v = τ.v0 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e := by
    intro v hv
    by_cases hface : v ∈ [τ.v0, τ.v2, τ.v3]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hface
      rcases hface with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · right; right; right
      have hv0 : v ≠ τ.v0 := by
        intro h; apply hface; simp [h]
      have hv2 : v ≠ τ.v2 := by
        intro h; apply hface; simp [h]
      have hv3 : v ≠ τ.v3 := by
        intro h; apply hface; simp [h]
      exact (he023unique v ⟨hv, hv0, hv2, hv3⟩).trans he023eq
  exact ⟨ρ012, ρ013, ρ023, e, hρ012K, hρ013K, hρ023K,
    he0, he1, he2, he3, heτ,
    h0_012, h1_012, h2_012, h0_013, h1_013, h3_013,
    h0_023, h2_023, h3_023, he012, he013, he023,
    h012Cover, h013Cover, h023Cover⟩

end Poincare
