import Poincare.VertexLinkThreeStarOffStarPartner
import Mathlib.Tactic

namespace Poincare

/-- The represented link triangles outside the star of x. -/
noncomputable def vertexLinkOffStarTriangles
    (K : Triangulation) (v x : Nat) : Finset LinkTriangle := by
  classical
  exact (vertexLinkTriangles K v).toFinset.filter
    (fun σ => σ ∉ vertexLinkStarTriangles K v x)

/-- Link adjacency restricted to off-star triangles. -/
def VertexLinkOffStarAdjacent
    (K : Triangulation) (v x : Nat)
    (σ ρ : LinkTriangle) : Prop :=
  σ ∈ vertexLinkOffStarTriangles K v x ∧
  ρ ∈ vertexLinkOffStarTriangles K v x ∧
  VertexLinkAdjacent K v σ ρ

/-- An actual off-star adjacency component containing a seed. -/
noncomputable def vertexLinkOffStarComponent
    (K : Triangulation) (v x : Nat)
    (σ : LinkTriangle) : Finset LinkTriangle := by
  classical
  exact (vertexLinkOffStarTriangles K v x).filter
    (fun ρ =>
      Relation.EqvGen (VertexLinkOffStarAdjacent K v x) σ ρ)

/-- All off-star adjacency components (deduplicated). -/
noncomputable def vertexLinkOffStarComponents
    (K : Triangulation) (v x : Nat) :
    Finset (Finset LinkTriangle) := by
  classical
  exact (vertexLinkOffStarTriangles K v x).image
    (vertexLinkOffStarComponent K v x)

/-- Every off-star triangle belongs to exactly one actual off-star component. -/
theorem vertexLinkOffStarComponents_unique_membership
    (K : Triangulation) (v x : Nat) :
    ∀ σ ∈ vertexLinkOffStarTriangles K v x,
      ∃! C : Finset LinkTriangle,
        C ∈ vertexLinkOffStarComponents K v x ∧ σ ∈ C := by
  classical
  let O := vertexLinkOffStarTriangles K v x
  let R := VertexLinkOffStarAdjacent K v x
  let comp := vertexLinkOffStarComponent K v x
  have hmem (a b : LinkTriangle) :
      b ∈ comp a ↔
        b ∈ O ∧ Relation.EqvGen R a b := by
    simp [O, R, comp, vertexLinkOffStarComponent]

  have heq (a b : LinkTriangle)
      (hab : Relation.EqvGen R a b) :
      comp a = comp b := by
    ext z
    rw [hmem, hmem]
    constructor
    · rintro ⟨hz, haz⟩
      exact ⟨hz, Relation.EqvGen.trans b a z
        (Relation.EqvGen.symm a b hab) haz⟩
    · rintro ⟨hz, hbz⟩
      exact ⟨hz, Relation.EqvGen.trans a b z hab hbz⟩

  have hmemC (C : Finset LinkTriangle) :
      C ∈ vertexLinkOffStarComponents K v x ↔
        ∃ a ∈ O, comp a = C := by
    change C ∈ O.image comp ↔ _
    exact Finset.mem_image

  intro σ hσ
  refine ⟨comp σ, ?_, ?_⟩
  · constructor
    · exact (hmemC (comp σ)).2 ⟨σ, hσ, rfl⟩
    · exact (hmem σ σ).2
        ⟨hσ, Relation.EqvGen.refl σ⟩
  · intro C hC
    obtain ⟨a, ha, heqC⟩ := (hmemC C).1 hC.1
    have hσa : σ ∈ comp a := by
      rw [heqC]
      exact hC.2
    have haσ : Relation.EqvGen R a σ :=
      ((hmem a σ).1 hσa).2
    exact heqC.symm.trans (heq a σ haσ)

end Poincare
