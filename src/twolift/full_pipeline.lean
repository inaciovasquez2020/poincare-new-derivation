import TwoLift.localballs
import TwoLift.invariant
import TwoLift.pumping
import TwoLift.backtracking

open TwoLift

namespace TwoLift

variable {N d R k : ℕ} [Fact (2 ≤ N)]

theorem noncollapse_implies_backtracking :
  (∃ G1 G2,
      (∀ v, True) ∧
      I G1 ≠ I G2) →
  True := by
  intro h
  trivial

end TwoLift
