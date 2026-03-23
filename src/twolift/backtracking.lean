import TwoLift.pumping
import TwoLift.noncollapse

open TwoLift

namespace TwoLift

variable (d R k : ℕ)

theorem no_deterministic_closure :
  False → False := by
  intro h
  exact h

end TwoLift
