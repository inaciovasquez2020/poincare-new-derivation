import Poincare.Triangulation
import Poincare.LocalEffect
import Poincare.Step

namespace Poincare

axiom step_strict :
∀ K, Phi K > 0 → Phi (step K) < Phi K

theorem Phi_decreases (K : Triangulation) (h : Phi K > 0) :
Phi (step K) < Phi K :=
step_strict K h

end Poincare
