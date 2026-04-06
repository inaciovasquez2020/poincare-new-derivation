import Poincare.Moves
import Poincare.MovesImpl
import Poincare.MovesSpec

namespace Poincare

theorem applyMoveImpl_preserves_allVerts :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMoveImpl K m) = allVerts K :=
  applyMoveImpl_spec

theorem selectMoveImpl_is_total :
  ∀ K : Triangulation, ∃ m : PachnerMove, m = selectMoveImpl K :=
  selectMoveImpl_total

end Poincare
