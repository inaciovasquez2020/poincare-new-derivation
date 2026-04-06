import Mathlib
import Poincare.Triangulation
import Poincare.PhiDecomposition

namespace Poincare

axiom vertexDefect_pos_implies_Phi_pos :
  ∀ (T : Triangulation) (v : Nat),
    vertexDefect T v > 0 → Phi T > 0

end Poincare
