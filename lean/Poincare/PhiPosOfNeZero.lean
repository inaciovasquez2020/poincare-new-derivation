import Poincare.Triangulation

namespace Poincare

theorem phi_pos_of_ne_zero :
  ∀ T : Triangulation, Phi T ≠ 0 → 0 < Phi T := by
  intro T h
  exact Nat.pos_of_ne_zero h

end Poincare
