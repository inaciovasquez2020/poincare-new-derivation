import Poincare.MovesAssumptions

namespace Poincare

theorem selectMove_spec_from_impl :
  ∀ K : Triangulation, Phi K > 0 → Phi (applyMove K (selectMove K)) < Phi K := by
  intro K hK
  rw [happly_impl, hselect_impl]
  exact selectMoveImpl_spec K hK

end Poincare
