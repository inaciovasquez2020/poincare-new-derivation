import Poincare.GlobalEdgeIncidenceThreeStarExtraction
import Mathlib.Tactic

namespace Poincare

/--
A nonempty off-star region closed under adjacencies to other off-star
triangles must meet the incidence-three star along a triangle adjacency.

This is a positivity lemma for off-star connected components. Its
closure hypothesis is the defining property that must be verified
when the regions are constructed as actual connected components.
It does not assert that crossings sum to three.
-/
theorem ClosedTriangulationCore.offStar_component_has_crossing
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hthree :
      (K.tets.filter (fun τ => v ∈ τ.verts ∧ x ∈ τ.verts)).length = 3)
    (hconnected : VertexLinkConnected K v)
    (C : Finset LinkTriangle)
    (hCnonempty : C.Nonempty)
    (hCsubset :
      ∀ σ ∈ C, σ ∈ vertexLinkTriangles K v)
    (hCoff :
      ∀ σ ∈ C, σ ∉ vertexLinkStarTriangles K v x)
    (hCclosed :
      ∀ σ ∈ C, ∀ ρ : LinkTriangle,
        VertexLinkAdjacent K v σ ρ →
        ρ ∉ vertexLinkStarTriangles K v x →
        ρ ∈ C) :
    ∃ σ ∈ C,
      ∃ ρ ∈ vertexLinkStarTriangles K v x,
        VertexLinkAdjacent K v σ ρ := by
  classical
  obtain ⟨σ, hσ⟩ := hCnonempty
  obtain ⟨ρ₀, ρ₁, ρ₂, hstar, _, _, _⟩ :=
    hcore.exists_three_distinct_vertexLinkStarTriangles_of_edgeIncidence_three
      v x hvx hthree
  have hρstar : ρ₀ ∈ vertexLinkStarTriangles K v x := by
    rw [hstar]
    simp
  have hρmem : ρ₀ ∈ vertexLinkTriangles K v :=
    ((mem_vertexLinkStarTriangles_iff K v x ρ₀).1 hρstar).1
  have hpath :
      Relation.ReflTransGen (VertexLinkAdjacent K v) σ ρ₀ :=
    hconnected σ (hCsubset σ hσ) ρ₀ hρmem
  by_contra hnone
  have hnoCross :
      ∀ a ∈ C,
        ∀ b ∈ vertexLinkStarTriangles K v x,
          ¬ VertexLinkAdjacent K v a b := by
    intro a ha b hb hab
    exact hnone ⟨a, ha, b, hb, hab⟩
  have hstay :
      ∀ {a b : LinkTriangle},
        Relation.ReflTransGen (VertexLinkAdjacent K v) a b →
        a ∈ C → b ∈ C := by
    intro a b hp
    induction hp with
    | refl =>
        intro ha
        exact ha
    | @tail a b c hprev hstep ih =>
        intro ha
        have hb : b ∈ C := ih ha
        by_cases hc : c ∈ vertexLinkStarTriangles K v x
        · exact (hnoCross b hb c hc hstep).elim
        · exact hCclosed b hb c hstep hc
  exact (hCoff ρ₀ (hstay hpath hσ)) hρstar

end Poincare
