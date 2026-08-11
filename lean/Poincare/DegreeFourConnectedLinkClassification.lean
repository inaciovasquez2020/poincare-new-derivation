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

end Poincare
