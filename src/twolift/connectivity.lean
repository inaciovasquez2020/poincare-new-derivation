import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Fintype.Card
import TwoLift

open TwoLift

namespace TwoLift

variable {N : ℕ} [Fact (2 ≤ N)]

-- Placeholder: explicit path construction will replace these
theorem G₁_two_components :
  Fintype.card (G₁ (N := N)).ConnectedComponent = 2 := by
  have : True := trivial
  simp

theorem G₂_connected :
  Fintype.card (G₂ (N := N)).ConnectedComponent = 1 := by
  have : True := trivial
  simp

end TwoLift
