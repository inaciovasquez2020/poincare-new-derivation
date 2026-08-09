import Poincare.Moves

namespace Poincare

def ClosedTriangulationCore (K : Triangulation) : Prop :=
  (∀ τ ∈ K.tets, τ.verts.Nodup) ∧

  K.tets.Pairwise
    (fun τ σ => ¬ SameTetVertices τ σ) ∧

  ∀ a b c : Nat,
    [a, b, c].Nodup →
    (∃ τ ∈ K.tets,
      a ∈ τ.verts ∧
      b ∈ τ.verts ∧
      c ∈ τ.verts) →
    (K.tets.filter
      (fun τ =>
        a ∈ τ.verts ∧
        b ∈ τ.verts ∧
        c ∈ τ.verts)).length = 2


theorem single_tet_not_ClosedTriangulationCore
    (τ : Tet)
    (hτ : τ.verts.Nodup) :
    ¬ ClosedTriangulationCore
      ({ tets := [τ] } : Triangulation) := by
  intro hcore

  have hface :
      [τ.v0, τ.v1, τ.v2].Nodup := by
    have h := hτ
    simp [Tet.verts] at h ⊢
    aesop

  have hrepresented :
      ∃ σ ∈ ([τ] : List Tet),
        τ.v0 ∈ σ.verts ∧
        τ.v1 ∈ σ.verts ∧
        τ.v2 ∈ σ.verts := by
    refine ⟨τ, by simp, ?_⟩
    simp [Tet.verts]

  have hincidence :=
    hcore.2.2
      τ.v0 τ.v1 τ.v2
      hface
      hrepresented

  norm_num [Tet.verts] at hincidence

end Poincare
