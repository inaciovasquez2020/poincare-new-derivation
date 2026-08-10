import Poincare.FiveTetGlobalClassification

namespace Poincare

deriving instance DecidableEq for Tet

/-- The global zero-defect five-tetrahedron classification, expressed as the
combinatorial boundary pattern of a four-simplex. -/
theorem ClosedTriangulationCore.exists_fourSimplexBoundary_combinatorial_certificate
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    (hconn : TetrahedronVertexOverlapConnected K)
    {τ : Tet}
    (hτK : τ ∈ K.tets)
    (hτ : τ.verts.Nodup) :
    ∃ ρ012 ρ013 ρ023 ρ123 e,
      ρ012 ∈ K.tets ∧
      ρ013 ∈ K.tets ∧
      ρ023 ∈ K.tets ∧
      ρ123 ∈ K.tets ∧
      e ∉ τ.verts ∧
      [τ.v0, τ.v1, τ.v2, τ.v3, e].Nodup ∧
      (∀ v : Nat, v ∈ vertexSupport K ↔
        v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e) ∧
      (vertexSupport K).toFinset = {τ.v0, τ.v1, τ.v2, τ.v3, e} ∧
      K.tets.toFinset = {τ, ρ012, ρ013, ρ023, ρ123} ∧
      τ.verts.toFinset = {τ.v0, τ.v1, τ.v2, τ.v3} ∧
      ρ012.verts.toFinset = {τ.v0, τ.v1, τ.v2, e} ∧
      ρ013.verts.toFinset = {τ.v0, τ.v1, τ.v3, e} ∧
      ρ023.verts.toFinset = {τ.v0, τ.v2, τ.v3, e} ∧
      ρ123.verts.toFinset = {τ.v1, τ.v2, τ.v3, e} ∧
      (∀ σ ∈ K.tets,
        σ.verts.toFinset = {τ.v0, τ.v1, τ.v2, τ.v3} ∨
        σ.verts.toFinset = {τ.v0, τ.v1, τ.v2, e} ∨
        σ.verts.toFinset = {τ.v0, τ.v1, τ.v3, e} ∨
        σ.verts.toFinset = {τ.v0, τ.v2, τ.v3, e} ∨
        σ.verts.toFinset = {τ.v1, τ.v2, τ.v3, e}) := by
  obtain ⟨ρ012, ρ013, ρ023, ρ123, e,
    h012K, h013K, h023K, h123K, heτ,
    h0_012, h1_012, h2_012, he012,
    h0_013, h1_013, h3_013, he013,
    h0_023, h2_023, h3_023, he023,
    h1_123, h2_123, h3_123, he123,
    h012Cover, h013Cover, h023Cover, h123Cover, hglobal⟩ :=
      hcore.exists_five_tet_global_classification_of_overlapConnected
        hPhi hconn hτK hτ
  have hdistinct : [τ.v0, τ.v1, τ.v2, τ.v3, e].Nodup := by
    rw [show [τ.v0, τ.v1, τ.v2, τ.v3, e] = τ.verts ++ [e] by
      rfl, List.nodup_append]
    refine ⟨hτ, by simp, ?_⟩
    intro a ha b hb hab
    have hbe : b = e := by simpa using hb
    apply heτ
    rw [← hbe, ← hab]
    exact ha
  have hsupport : ∀ v : Nat, v ∈ vertexSupport K ↔
      v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e := by
    intro v
    rw [mem_vertexSupport_iff]
    constructor
    · intro hv
      obtain ⟨σ, hσK, hvσ⟩ := List.mem_flatMap.mp hv
      rcases hglobal σ hσK with rfl | rfl | rfl | rfl | rfl
      · have h := (show v = σ.v0 ∨ v = σ.v1 ∨ v = σ.v2 ∨ v = σ.v3 by
          simpa [Tet.verts] using hvσ)
        rcases h with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases h012Cover v hvσ with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · rcases h013Cover v hvσ with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · rcases h023Cover v hvσ with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · rcases h123Cover v hvσ with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · intro hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact List.mem_flatMap.mpr ⟨τ, hτK, by simp [Tet.verts]⟩
      · exact List.mem_flatMap.mpr ⟨τ, hτK, by simp [Tet.verts]⟩
      · exact List.mem_flatMap.mpr ⟨τ, hτK, by simp [Tet.verts]⟩
      · exact List.mem_flatMap.mpr ⟨τ, hτK, by simp [Tet.verts]⟩
      · exact List.mem_flatMap.mpr ⟨ρ012, h012K, he012⟩
  have hsupportFinset : (vertexSupport K).toFinset =
      {τ.v0, τ.v1, τ.v2, τ.v3, e} := by
    ext v
    simpa only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton] using
      hsupport v
  have htetsFinset : K.tets.toFinset = {τ, ρ012, ρ013, ρ023, ρ123} := by
    ext σ
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact hglobal σ
    · intro h
      rcases h with rfl | rfl | rfl | rfl | rfl
      · exact hτK
      · exact h012K
      · exact h013K
      · exact h023K
      · exact h123K
  have hτFinset : τ.verts.toFinset = {τ.v0, τ.v1, τ.v2, τ.v3} := by
    simp [Tet.verts]
  have h012Finset : ρ012.verts.toFinset = {τ.v0, τ.v1, τ.v2, e} := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact h012Cover v
    · intro h
      rcases h with rfl | rfl | rfl | rfl
      · exact h0_012
      · exact h1_012
      · exact h2_012
      · exact he012
  have h013Finset : ρ013.verts.toFinset = {τ.v0, τ.v1, τ.v3, e} := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact h013Cover v
    · intro h
      rcases h with rfl | rfl | rfl | rfl
      · exact h0_013
      · exact h1_013
      · exact h3_013
      · exact he013
  have h023Finset : ρ023.verts.toFinset = {τ.v0, τ.v2, τ.v3, e} := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact h023Cover v
    · intro h
      rcases h with rfl | rfl | rfl | rfl
      · exact h0_023
      · exact h2_023
      · exact h3_023
      · exact he023
  have h123Finset : ρ123.verts.toFinset = {τ.v1, τ.v2, τ.v3, e} := by
    ext v
    simp only [List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact h123Cover v
    · intro h
      rcases h with rfl | rfl | rfl | rfl
      · exact h1_123
      · exact h2_123
      · exact h3_123
      · exact he123
  refine ⟨ρ012, ρ013, ρ023, ρ123, e,
    h012K, h013K, h023K, h123K, heτ, hdistinct, hsupport,
    hsupportFinset, htetsFinset, hτFinset, h012Finset, h013Finset,
    h023Finset, h123Finset, ?_⟩
  intro σ hσK
  rcases hglobal σ hσK with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hτFinset
  · exact Or.inr (Or.inl h012Finset)
  · exact Or.inr (Or.inr (Or.inl h013Finset))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h023Finset)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h123Finset)))

end Poincare
