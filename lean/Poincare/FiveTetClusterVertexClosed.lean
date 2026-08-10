import Poincare.FiveTetClusterStarSaturation

namespace Poincare

/-- The five-tetrahedron cluster supplied by zero defect is closed under
incidence at any of its five vertices. -/
theorem ClosedTriangulationCore.exists_five_tet_cluster_vertex_closed
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
      (∀ σ ∈ K.tets, e ∈ σ.verts → σ = ρ012 ∨ σ = ρ013 ∨ σ = ρ023 ∨ σ = ρ123) ∧
      (∀ σ ∈ K.tets,
        (τ.v0 ∈ σ.verts ∨ τ.v1 ∈ σ.verts ∨ τ.v2 ∈ σ.verts ∨
          τ.v3 ∈ σ.verts ∨ e ∈ σ.verts) →
        σ = τ ∨ σ = ρ012 ∨ σ = ρ013 ∨ σ = ρ023 ∨ σ = ρ123) := by
  obtain ⟨ρ012, ρ013, ρ023, ρ123, e,
    h012K, h013K, h023K, h123K, heτ,
    h0_012, h1_012, h2_012, he012,
    h0_013, h1_013, h3_013, he013,
    h0_023, h2_023, h3_023, he023,
    h1_123, h2_123, h3_123, he123,
    h012Cover, h013Cover, h023Cover, h123Cover,
    hstar0, hstar1, hstar2, hstar3, hstare⟩ :=
      hcore.exists_five_tet_cluster_star_saturation hPhi hτK hτ
  refine ⟨ρ012, ρ013, ρ023, ρ123, e,
    h012K, h013K, h023K, h123K, heτ,
    h0_012, h1_012, h2_012, he012,
    h0_013, h1_013, h3_013, he013,
    h0_023, h2_023, h3_023, he023,
    h1_123, h2_123, h3_123, he123,
    h012Cover, h013Cover, h023Cover, h123Cover,
    hstar0, hstar1, hstar2, hstar3, hstare, ?_⟩
  intro σ hσK hvertex
  rcases hvertex with h0 | h1 | h2 | h3 | he
  · rcases hstar0 σ hσK h0 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases hstar1 σ hσK h1 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rcases hstar2 σ hσK h2 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rcases hstar3 σ hσK h3 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rcases hstare σ hσK he with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end Poincare
