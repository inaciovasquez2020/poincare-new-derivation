import Mathlib
import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedySpec

namespace Poincare

def edge_imbalance_measure (T : Triangulation) : Nat := Phi T

def edge_flip (T : Triangulation) (_ : Nat) : Triangulation :=
  applyMoveImpl T (selectMoveImplGreedy T)

/-
BOUNDARY := ¬ ∀ T : Triangulation,
  edge_imbalance_measure T > 0 →
  ∃ e : Nat,
    edge_imbalance_measure (edge_flip T e) <
      edge_imbalance_measure T

The current edge_flip is the identity-based greedy implementation, so the
strict edge descent claim is unavailable.
-/

end Poincare
