import Poincare.VertexLinkOffStarComponentsPartition
import Mathlib.Tactic

namespace Poincare

/--
A perimeter edge of an incidence-three vertex-link star has one off-star
partner, and that partner belongs to exactly one actual off-star adjacency
component. The partner and the component are derived from the closed-core
incidence theorem and the actual EqvGen-based component construction.
-/
theorem ClosedTriangulationCore.perimeterEdge_exists_unique_offStar_component
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (e : LinkEdge)
    (hperimeter :
      (∃ σ ∈ vertexLinkStarTriangles K v x, e.InTriangle σ) ∧
        ¬ (x = e.lo ∨ x = e.hi)) :
    ∃! C : Finset LinkTriangle,
      C ∈ vertexLinkOffStarComponents K v x ∧
      ∃ ρ : LinkTriangle,
        ρ ∈ vertexLinkTriangles K v ∧
        e.InTriangle ρ ∧
        ρ ∉ vertexLinkStarTriangles K v x ∧
        ρ ∈ C := by
  classical
  obtain ⟨ρ, ⟨hρlink, heρ, hρoff⟩, hρunique⟩ :=
    hcore.perimeterEdge_exists_unique_offStar_partner v x e hperimeter
  have hρO : ρ ∈ vertexLinkOffStarTriangles K v x := by
    simp [vertexLinkOffStarTriangles, hρlink, hρoff]
  obtain ⟨C, ⟨hCmem, hρC⟩, hCunique⟩ :=
    vertexLinkOffStarComponents_unique_membership K v x ρ hρO
  refine ⟨C, ?_, ?_⟩
  · exact ⟨hCmem, ρ, hρlink, heρ, hρoff, hρC⟩
  · intro D hD
    obtain ⟨hDmem, ρ', hρ'link, heρ', hρ'off, hρ'D⟩ := hD
    have hρ'eq : ρ' = ρ :=
      hρunique ρ' ⟨hρ'link, heρ', hρ'off⟩
    subst ρ'
    exact hCunique D ⟨hDmem, hρ'D⟩

end Poincare
