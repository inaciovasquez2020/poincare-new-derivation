import Poincare.FiveTetClusterVertexClosed
import Poincare.TriangulationTopologicalGeometricConnectedness

namespace Poincare

/-- Under connectedness of the represented tetrahedron overlap graph, the
five-tetrahedron cluster forced by zero defect contains every represented
tetrahedron. -/
theorem ClosedTriangulationCore.exists_five_tet_global_classification_of_overlapConnected
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
      τ.v0 ∈ ρ012.verts ∧
      τ.v1 ∈ ρ012.verts ∧
      τ.v2 ∈ ρ012.verts ∧
      e ∈ ρ012.verts ∧
      τ.v0 ∈ ρ013.verts ∧
      τ.v1 ∈ ρ013.verts ∧
      τ.v3 ∈ ρ013.verts ∧
      e ∈ ρ013.verts ∧
      τ.v0 ∈ ρ023.verts ∧
      τ.v2 ∈ ρ023.verts ∧
      τ.v3 ∈ ρ023.verts ∧
      e ∈ ρ023.verts ∧
      τ.v1 ∈ ρ123.verts ∧
      τ.v2 ∈ ρ123.verts ∧
      τ.v3 ∈ ρ123.verts ∧
      e ∈ ρ123.verts ∧
      (∀ v ∈ ρ012.verts,
        v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v2 ∨ v = e) ∧
      (∀ v ∈ ρ013.verts,
        v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v3 ∨ v = e) ∧
      (∀ v ∈ ρ023.verts,
        v = τ.v0 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e) ∧
      (∀ v ∈ ρ123.verts,
        v = τ.v1 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e) ∧
      (∀ σ ∈ K.tets,
        σ = τ ∨
        σ = ρ012 ∨
        σ = ρ013 ∨
        σ = ρ023 ∨
        σ = ρ123) := by
  obtain ⟨ρ012, ρ013, ρ023, ρ123, e,
    h012K, h013K, h023K, h123K, heτ,
    h0_012, h1_012, h2_012, he012,
    h0_013, h1_013, h3_013, he013,
    h0_023, h2_023, h3_023, he023,
    h1_123, h2_123, h3_123, he123,
    h012Cover, h013Cover, h023Cover, h123Cover,
    _hstar0, _hstar1, _hstar2, _hstar3, _hstare, hclosed⟩ :=
      hcore.exists_five_tet_cluster_vertex_closed hPhi hτK hτ
  let ClusterTet : Tet → Prop := fun σ ↦
    σ = τ ∨ σ = ρ012 ∨ σ = ρ013 ∨ σ = ρ023 ∨ σ = ρ123
  have hoverlap : ∀ α β,
      ClusterTet α →
      ((α.verts.toFinset ∩ β.verts.toFinset).Nonempty ∧ α ∈ K.tets) →
      β ∈ K.tets → ClusterTet β := by
    intro α β hα hαβ hβK
    obtain ⟨v, hv⟩ := hαβ.1
    have hvα : v ∈ α.verts :=
      List.mem_toFinset.mp (Finset.mem_inter.mp hv).1
    have hvβ : v ∈ β.verts :=
      List.mem_toFinset.mp (Finset.mem_inter.mp hv).2
    have hvCluster :
        v = τ.v0 ∨ v = τ.v1 ∨ v = τ.v2 ∨ v = τ.v3 ∨ v = e := by
      rcases hα with rfl | rfl | rfl | rfl | rfl
      · have hvτ :
            v = α.v0 ∨ v = α.v1 ∨ v = α.v2 ∨ v = α.v3 := by
          simpa [Tet.verts] using hvα
        rcases hvτ with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases h012Cover v hvα with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · rcases h013Cover v hvα with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · rcases h023Cover v hvα with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · rcases h123Cover v hvα with h | h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    apply hclosed β hβK
    rcases hvCluster with h | h | h | h | h
    · exact Or.inl (h ▸ hvβ)
    · exact Or.inr (Or.inl (h ▸ hvβ))
    · exact Or.inr (Or.inr (Or.inl (h ▸ hvβ)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h ▸ hvβ))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h ▸ hvβ))))
  refine ⟨ρ012, ρ013, ρ023, ρ123, e,
    h012K, h013K, h023K, h123K, heτ,
    h0_012, h1_012, h2_012, he012,
    h0_013, h1_013, h3_013, he013,
    h0_023, h2_023, h3_023, he023,
    h1_123, h2_123, h3_123, he123,
    h012Cover, h013Cover, h023Cover, h123Cover, ?_⟩
  intro σ hσK
  have hpath := hconn.2 τ hτK σ hσK
  apply Relation.ReflTransGen.head_induction_on
    (motive := fun α _ ↦ α ∈ K.tets → ClusterTet α → ClusterTet σ)
    hpath
  · intro _ hcluster
    exact hcluster
  · intro α β hstep hrest ih hαK hα
    have hβK : β ∈ K.tets := by
      rcases hrest.cases_head with h | ⟨γ, hβγ, _⟩
      · simpa [h] using hσK
      · exact hβγ.2
    exact ih hβK (hoverlap α β hα hstep hβK)
  · exact hτK
  · exact Or.inl rfl

end Poincare
