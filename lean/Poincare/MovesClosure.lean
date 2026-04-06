import Poincare.Moves
import Poincare.MovesImpl
import Poincare.MovesSpec
import Poincare.Triangulation

namespace Poincare

theorem abstract_applyMove_from_impl
  (happly : applyMove = applyMoveImpl) :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMove K m) = allVerts K := by
  intro K m
  rw [happly]
  exact applyMoveImpl_spec K m

theorem abstract_selectMove_total_from_impl
  (hselect : selectMove = selectMoveImpl) :
  ∀ K : Triangulation, ∃ m : PachnerMove, m = selectMove K := by
  intro K
  rw [hselect]
  exact selectMoveImpl_total K

end Poincare
