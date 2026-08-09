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

end Poincare
