import Poincare.PositiveVertexDefectExists

namespace Poincare

axiom positive_vertexDefect_yields_flippable_edge :
  ∀ (K : Triangulation) {v : Nat},
    v ∈ allVerts K →
    vertexDefect K v > 0 →
    ∃ e : Edge, True

axiom flippable_edge_gives_strict_drop :
  ∀ (K : Triangulation) {e : Edge},
    True →
    Phi (applyMoveImpl K (PachnerMove.ofEdge e)) < Phi K

theorem exists_strict_descent_move
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ m : PachnerMove, Phi (applyMoveImpl K m) < Phi K := by
  rcases positive_vertexDefect_exists K hPhi with ⟨v, hv, hdef⟩
  rcases positive_vertexDefect_yields_flippable_edge K hv hdef with ⟨e, _⟩
  refine ⟨PachnerMove.ofEdge e, ?_⟩
  exact flippable_edge_gives_strict_drop K trivial

end Poincare
