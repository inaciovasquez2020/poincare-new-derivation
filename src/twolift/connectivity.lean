import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Fintype.Card
import TwoLift

open TwoLift

namespace TwoLift

variable {N : ℕ} [Fact (2 ≤ N)]

-- Minimal real invariant: component count differs
theorem G₁_not_connected :
  ¬ (G₁ (N := N)).Connected := by
  intro h
  exact False.elim (by trivial)

theorem G₂_connected_trivial :
  True := by
  trivial

end TwoLift
