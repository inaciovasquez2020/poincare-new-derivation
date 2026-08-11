import Poincare.DegreeFourVertexLinkClassification

namespace Poincare

/-- In a connected vertex link, a nonempty family of represented link
triangles that is closed under link adjacency contains every represented link
triangle.  This is the propagation principle that excludes an additional
four-simplex block meeting a degree-four boundary cluster only at a vertex. -/
theorem VertexLinkConnected.all_of_adjacent_closed
    {K : Triangulation}
    {v : Nat}
    (hconnected : VertexLinkConnected K v)
    (C : LinkTriangle → Prop)
    {σ₀ : LinkTriangle}
    (hσ₀ : σ₀ ∈ vertexLinkTriangles K v)
    (hC₀ : C σ₀)
    (hclosed : ∀ σ ρ,
      VertexLinkAdjacent K v σ ρ → C σ → C ρ) :
    ∀ ρ ∈ vertexLinkTriangles K v, C ρ := by
  intro ρ hρ
  have hpath := hconnected σ₀ hσ₀ ρ hρ
  exact Relation.ReflTransGen.trans_induction_on
    (motive := fun {σ ρ} _ => C σ → C ρ)
    hpath
    (fun _ hC => hC)
    (fun hadj hC => hclosed _ _ hadj hC)
    (fun _ _ ih₁ ih₂ hC => ih₂ (ih₁ hC))
    hC₀

/-- In the target-present branch at a degree-four center, the four source
tetrahedra fill the entire represented vertex link.  The target witness is
kept explicit, so this is precisely the local five-tetrahedron cluster
statement and makes no assertion about tetrahedra away from the center. -/
theorem Move41Site.targetPresent_fiveTetCluster_closes_vertexLink
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {v : Nat}
    (hdegree : vertexDegree K v = 4)
    (hconnected : VertexLinkConnected K v)
    (s : Move41Site)
    (hse : s.e = v)
    (hsaturated : ∀ τ ∈ K.tets, s.e ∈ τ.verts →
      ∃ source ∈ s.sourceTets, SameTetVertices τ source)
    (htarget : ∃ τ ∈ K.tets, SameTetVertices τ s.targetTet) :
    (∃ τ ∈ K.tets, SameTetVertices τ s.targetTet) ∧
      ∀ σ ∈ vertexLinkTriangles K v,
        ∃ τ ∈ K.tets,
          τ.linkTriangleAt? v = some σ ∧
          ∃ source ∈ s.sourceTets, SameTetVertices τ source := by
  classical
  refine ⟨htarget, ?_⟩
  let C : LinkTriangle → Prop := fun σ ↦
    ∃ τ ∈ K.tets,
      τ.linkTriangleAt? v = some σ ∧
      ∃ source ∈ s.sourceTets, SameTetVertices τ source
  have hlength : (vertexLinkTriangles K v).length = 4 := by
    rw [vertexLinkTriangles_length_eq_vertexDegree K hcore v, hdegree]
  have hnonempty : (vertexLinkTriangles K v).length > 0 := by omega
  obtain ⟨σ₀, hσ₀⟩ := List.length_pos_iff_exists_mem.mp hnonempty
  have hC_of_mem : ∀ σ ∈ vertexLinkTriangles K v, C σ := by
    intro σ hσ
    obtain ⟨τ, hτK, hlink⟩ :=
      (mem_vertexLinkTriangles_iff K v σ).1 hσ
    have hvτ : v ∈ τ.verts :=
      (τ.linkTriangleAt?_isSome_iff v).1 (by rw [hlink]; rfl)
    obtain ⟨source, hsource, hsame⟩ :=
      hsaturated τ hτK (hse.symm ▸ hvτ)
    exact ⟨τ, hτK, hlink, source, hsource, hsame⟩
  have hC₀ : C σ₀ := hC_of_mem σ₀ hσ₀
  have hclosed : ∀ σ ρ,
      VertexLinkAdjacent K v σ ρ → C σ → C ρ := by
    intro σ ρ hadj _
    exact hC_of_mem ρ hadj.2.1
  exact hconnected.all_of_adjacent_closed C hσ₀ hC₀ hclosed

end Poincare
