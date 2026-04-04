import Poincare.Triangulation

namespace Poincare

axiom phi_pos_of_ne_zero :
  ∀ T : Triangulation, Phi T ≠ 0 → 0 < Phi T

end Poincare
