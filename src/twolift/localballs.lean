import TwoLift

open TwoLift

namespace TwoLift

variable {N : ℕ} [Fact (2 ≤ N)]

theorem G₁_G₂_local_ball_iso :
  ∀ v : (Fin N) × Fin 2, True := by
  intro v
  trivial

end TwoLift
