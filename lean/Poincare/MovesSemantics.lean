import Poincare.AxiomFrontier

namespace Poincare

theorem applyMove_spec :
  ∀ (K : Triangulation) (m : PachnerMove), allVerts (applyMove K m) = allVerts K :=
  applyMove_spec_available

theorem selectMove_spec :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMove K (selectMove K)) < Phi K :=
  selectMove_spec_available

theorem selected_move_strict_descent :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMove K (selectMove K)) < Phi K := by
  intro K hK
  exact selectMove_spec K hK

end Poincare
