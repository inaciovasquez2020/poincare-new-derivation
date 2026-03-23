import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import TwoLift
import TwoLift.connectivity

open TwoLift

namespace TwoLift

variable {N : ℕ} [Fintype (Fin N)] [Fact (2 ≤ N)]

theorem I_G₁_ne_I_G₂ :
  I (G₁ (N := N)) ≠ I (G₂ (N := N)) := by
  sorry

end TwoLift
