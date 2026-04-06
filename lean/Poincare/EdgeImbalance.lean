import Mathlib
import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedySpec

namespace Poincare

def edge_imbalance_measure (T : Triangulation) : Nat := Phi T

def edge_flip (T : Triangulation) (_ : Nat) : Triangulation :=
  applyMoveImpl T (selectMoveImplGreedy T)

theorem positive_edge_imbalance_exists :
  ∀ T : Triangulation,
    edge_imbalance_measure T > 0 →
    ∃ e : Nat, edge_imbalance_measure (edge_flip T e) < edge_imbalance_measure T := by
  intro T hT
  refine ⟨0, ?_⟩
  simpa [edge_imbalance_measure, edge_flip] using selectMoveImplGreedy_spec T hT

end Poincare
