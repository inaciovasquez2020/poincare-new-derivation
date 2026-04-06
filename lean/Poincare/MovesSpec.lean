import Poincare.Triangulation
import Poincare.MovesImpl

namespace Poincare

theorem applyMoveImpl_spec :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMoveImpl K m) = allVerts K := by
  intro K m
  rfl

theorem selectMoveImpl_total :
  ∀ K : Triangulation, ∃ m : PachnerMove, m = selectMoveImpl K := by
  intro K
  exact ⟨selectMoveImpl K, rfl⟩

end Poincare
