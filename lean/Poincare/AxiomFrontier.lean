import Poincare.Moves
import Poincare.MovesDerivedNoCycle

namespace Poincare

theorem applyMove_spec_available :
  ∀ (K : Triangulation) (m : PachnerMove),
    allVerts (applyMove K m) = allVerts K :=
  applyMove_spec_derived_nocycle


end Poincare
