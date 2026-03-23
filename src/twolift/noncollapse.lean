import TwoLift
import TwoLift.invariant

open TwoLift

namespace TwoLift

variable {N : ℕ} [Fintype (Fin N)] [Fact (2 ≤ N)]

theorem noncollapse_witness :
  ∃ (G1 G2 : SimpleGraph ((Fin N) × Fin 2)),
    I G1 ≠ I G2 := by
  exact ⟨G₁ (N := N), G₂ (N := N), I_G₁_ne_I_G₂⟩

end TwoLift
