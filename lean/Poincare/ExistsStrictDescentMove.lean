import Poincare.PositiveVertexDefectExists
import Poincare.MovesAssumptions

namespace Poincare

theorem exists_strict_descent_move
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ m : PachnerMove, Phi (applyMoveImpl K m) < Phi K := by
  rcases positive_vertexDefect_exists K hPhi with ⟨v, hv, hdef⟩
  rcases positive_vertexDefect_yields_flippable_edge K hv hdef with ⟨e, hflip⟩
  refine ⟨PachnerMove.ofEdge e, ?_⟩
  simpa using flippable_edge_gives_strict_drop K hflip

end Poincare
