import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import TwoLift

open TwoLift

namespace TwoLift

variable {N : ℕ} [Fact (2 ≤ N)]

theorem G₁_two_components :
  Fintype.card (G₁ (N := N)).ConnectedComponent = 2 := by
  sorry

theorem G₂_connected :
  Fintype.card (G₂ (N := N)).ConnectedComponent = 1 := by
  sorry

end TwoLift
