import Poincare.GlobalEdgeIncidenceStarCount
import Mathlib.Tactic

namespace Poincare

private theorem exists_three_of_length_eq_three
    {α : Type}
    (l : List α)
    (h : l.length = 3) :
    ∃ a b c : α,
      l = [a, b, c] := by

  cases l with

  | nil =>
      simp at h

  | cons a l =>

      cases l with

      | nil =>
          simp at h

      | cons b l =>

          cases l with

          | nil =>
              simp at h

          | cons c l =>

              cases l with

              | nil =>
                  exact ⟨a, b, c, rfl⟩

              | cons d l =>
                  simp at h

/--
If the ambient edge `{v,x}` has tetrahedron-incidence exactly three,
then its represented star inside `Lk(v)` consists of exactly three
pairwise distinct link triangles.
-/
theorem
    ClosedTriangulationCore.exists_three_distinct_vertexLinkStarTriangles_of_edgeIncidence_three
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
      vertexLinkStarTriangles K v x =
        [σ₀, σ₁, σ₂] ∧
      σ₀ ≠ σ₁ ∧
      σ₀ ≠ σ₂ ∧
      σ₁ ≠ σ₂ := by

  have hlen :
      (vertexLinkStarTriangles K v x).length = 3 :=
    hcore.vertexLinkStarTriangles_length_eq_three_of_edgeIncidence_three
      v x hvx hthree

  have hnodup :
      (vertexLinkStarTriangles K v x).Nodup := by
    unfold vertexLinkStarTriangles
    apply List.Nodup.filter
    exact
      vertexLinkTriangles_nodup
        K hcore v

  obtain
    ⟨σ₀, σ₁, σ₂, hstar⟩ :=
    exists_three_of_length_eq_three
      (vertexLinkStarTriangles K v x)
      hlen

  rw [hstar] at hnodup

  have hpair :
      (σ₀ ≠ σ₁ ∧ σ₀ ≠ σ₂) ∧
        σ₁ ≠ σ₂ := by
    simpa using hnodup

  exact
    ⟨σ₀, σ₁, σ₂,
      hstar,
      hpair.1.1,
      hpair.1.2,
      hpair.2⟩

/--
Membership classification for the exact incidence-three star.
-/
theorem
    ClosedTriangulationCore.exists_three_vertexLinkStarTriangles_mem_iff_of_edgeIncidence_three
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
      ∀ σ : LinkTriangle,
        σ ∈ vertexLinkStarTriangles K v x ↔
          σ = σ₀ ∨
          σ = σ₁ ∨
          σ = σ₂ := by

  obtain
    ⟨σ₀, σ₁, σ₂,
      hstar,
      h01,
      h02,
      h12⟩ :=
    hcore.exists_three_distinct_vertexLinkStarTriangles_of_edgeIncidence_three
      v x hvx hthree

  refine
    ⟨σ₀, σ₁, σ₂,
      h01, h02, h12, ?_⟩

  intro σ

  rw [hstar]
  simp

/--
The three extracted triangles are genuine represented link triangles
and each contains the second ambient edge endpoint `x`.
-/
theorem
    ClosedTriangulationCore.exists_three_vertexLinkStarTriangles_with_support_of_edgeIncidence_three
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
      σ₀ ∈ vertexLinkTriangles K v ∧
      σ₁ ∈ vertexLinkTriangles K v ∧
      σ₂ ∈ vertexLinkTriangles K v ∧
      x ∈ σ₀.verts ∧
      x ∈ σ₁.verts ∧
      x ∈ σ₂.verts := by

  obtain
    ⟨σ₀, σ₁, σ₂,
      hstar,
      h01,
      h02,
      h12⟩ :=
    hcore.exists_three_distinct_vertexLinkStarTriangles_of_edgeIncidence_three
      v x hvx hthree

  have h₀ :
      σ₀ ∈ vertexLinkStarTriangles K v x := by
    rw [hstar]
    simp

  have h₁ :
      σ₁ ∈ vertexLinkStarTriangles K v x := by
    rw [hstar]
    simp

  have h₂ :
      σ₂ ∈ vertexLinkStarTriangles K v x := by
    rw [hstar]
    simp

  have hs₀ :=
    (mem_vertexLinkStarTriangles_iff
      K v x σ₀).1 h₀

  have hs₁ :=
    (mem_vertexLinkStarTriangles_iff
      K v x σ₁).1 h₁

  have hs₂ :=
    (mem_vertexLinkStarTriangles_iff
      K v x σ₂).1 h₂

  exact
    ⟨σ₀, σ₁, σ₂,
      h01, h02, h12,
      hs₀.1,
      hs₁.1,
      hs₂.1,
      hs₀.2,
      hs₁.2,
      hs₂.2⟩

end Poincare
