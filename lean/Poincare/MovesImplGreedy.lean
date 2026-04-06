import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

def selectMoveImplGreedy (_K : Triangulation) : PachnerMove :=
  PachnerMove.move23

theorem selectMoveImplGreedy_total :
  ∀ K : Triangulation, ∃ m : PachnerMove, m = selectMoveImplGreedy K := by
  intro K
  exact ⟨selectMoveImplGreedy K, rfl⟩

end Poincare
