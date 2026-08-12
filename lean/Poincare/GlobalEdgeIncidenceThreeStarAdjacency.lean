import Poincare.GlobalEdgeIncidenceThreeStarExtraction
import Mathlib.Tactic

namespace Poincare

private theorem
    vertexLinkStarDegreeTwo_adjacent_to_both_of_exact_three
    {K : Triangulation}
    {v x : Nat}
    {σ₀ σ₁ σ₂ : LinkTriangle}
    (hdeg :
      VertexLinkStarDegreeTwo K v x)
    (hσ₀ :
      σ₀ ∈ vertexLinkStarTriangles K v x)
    (hmem :
      ∀ σ : LinkTriangle,
        σ ∈ vertexLinkStarTriangles K v x ↔
          σ = σ₀ ∨ σ = σ₁ ∨ σ = σ₂)
    (hne01 : σ₀ ≠ σ₁)
    (hne02 : σ₀ ≠ σ₂)
    (hne12 : σ₁ ≠ σ₂) :
    VertexLinkStarAdjacent K v x σ₀ σ₁ ∧
      VertexLinkStarAdjacent K v x σ₀ σ₂ := by

  obtain
    ⟨ρ₁, ρ₂,
      hρ₁ne,
      hρ₂ne,
      hρ₁ρ₂,
      hadj₁,
      hadj₂,
      _⟩ :=
    hdeg σ₀ hσ₀

  have hρ₁mem :
      ρ₁ ∈ vertexLinkStarTriangles K v x :=
    hadj₁.2.1

  have hρ₂mem :
      ρ₂ ∈ vertexLinkStarTriangles K v x :=
    hadj₂.2.1

  have hρ₁cases :
      ρ₁ = σ₀ ∨
      ρ₁ = σ₁ ∨
      ρ₁ = σ₂ :=
    (hmem ρ₁).1 hρ₁mem

  have hρ₂cases :
      ρ₂ = σ₀ ∨
      ρ₂ = σ₁ ∨
      ρ₂ = σ₂ :=
    (hmem ρ₂).1 hρ₂mem

  rcases hρ₁cases with h10 | h11 | h12

  · exact
      (hρ₁ne h10).elim

  · have hρ₂eq :
        ρ₂ = σ₂ := by

      rcases hρ₂cases with h20 | h21 | h22

      · exact
          (hρ₂ne h20).elim

      · exact
          (hρ₁ρ₂
            (h11.trans h21.symm)).elim

      · exact h22

    constructor

    · simpa [h11] using hadj₁

    · simpa [hρ₂eq] using hadj₂

  · have hρ₂eq :
        ρ₂ = σ₁ := by

      rcases hρ₂cases with h20 | h21 | h22

      · exact
          (hρ₂ne h20).elim

      · exact h21

      · exact
          (hρ₁ρ₂
            (h12.trans h22.symm)).elim

    constructor

    · simpa [hρ₂eq] using hadj₂

    · simpa [h12] using hadj₁

/--
A closed-core ambient edge of tetrahedron-incidence three gives exactly
three represented link triangles, and the degree-two star condition forces
those three triangles to be pairwise adjacent.
-/
theorem
    ClosedTriangulationCore.exists_three_pairwiseAdjacent_vertexLinkStarTriangles_of_edgeIncidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (hvx : v ≠ x)
    (hthree :
      (K.tets.filter
        (fun τ =>
          v ∈ τ.verts ∧
          x ∈ τ.verts)).length = 3) :
    ∃ σ₀ σ₁ σ₂ : LinkTriangle,
      σ₀ ≠ σ₁ ∧
      σ₀ ≠ σ₂ ∧
      σ₁ ≠ σ₂ ∧
      VertexLinkStarAdjacent K v x σ₀ σ₁ ∧
      VertexLinkStarAdjacent K v x σ₀ σ₂ ∧
      VertexLinkStarAdjacent K v x σ₁ σ₂ := by

  obtain
    ⟨σ₀, σ₁, σ₂,
      h01,
      h02,
      h12,
      hmem⟩ :=
    hcore.exists_three_vertexLinkStarTriangles_mem_iff_of_edgeIncidence_three
      v x hvx hthree

  have hrep :
      VertexLinkVertexRepresented K v x :=
    (hcore.vertexLinkVertexRepresented_and_star_length_three_of_edgeIncidence_three
      v x hvx hthree).1

  have hdeg :
      VertexLinkStarDegreeTwo K v x :=
    hcore.vertexLinkStarDegreeTwo hrep

  have hσ₀ :
      σ₀ ∈ vertexLinkStarTriangles K v x :=
    (hmem σ₀).2
      (Or.inl rfl)

  have hσ₁ :
      σ₁ ∈ vertexLinkStarTriangles K v x :=
    (hmem σ₁).2
      (Or.inr (Or.inl rfl))

  have hfirst :=
    vertexLinkStarDegreeTwo_adjacent_to_both_of_exact_three
      hdeg
      hσ₀
      hmem
      h01
      h02
      h12

  have hmem₁ :
      ∀ σ : LinkTriangle,
        σ ∈ vertexLinkStarTriangles K v x ↔
          σ = σ₁ ∨ σ = σ₀ ∨ σ = σ₂ := by
    intro σ
    rw [hmem σ]
    aesop

  have hsecond :=
    vertexLinkStarDegreeTwo_adjacent_to_both_of_exact_three
      hdeg
      hσ₁
      hmem₁
      (Ne.symm h01)
      h12
      h02

  exact
    ⟨σ₀, σ₁, σ₂,
      h01, h02, h12,
      hfirst.1,
      hfirst.2,
      hsecond.2⟩

end Poincare
