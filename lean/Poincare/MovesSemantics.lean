import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

axiom applyMove_spec :
  ∀ (K : Triangulation) (m : PachnerMove), allVerts (applyMove K m) = allVerts K

axiom selectMove_spec :
  ∀ K : Triangulation, True

end Poincare
