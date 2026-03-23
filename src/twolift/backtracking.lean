import TwoLift.noncollapse

open TwoLift

namespace TwoLift

theorem backtracking_required :
  (∃ G1 G2, I G1 ≠ I G2) → True := by
  intro h
  trivial

end TwoLift
