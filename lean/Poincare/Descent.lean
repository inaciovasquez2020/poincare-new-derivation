import Poincare.Triangulation
import Poincare.Moves
import Poincare.AxiomFrontier

namespace Poincare

theorem step_strict :
  ∀ K, Phi K > 0 →
    ∃ m : PachnerMove, Phi (applyMove K m) < Phi K := by
  intro K hpos
  refine ⟨selectMove K, ?_⟩
  exact selectMove_spec_available K hpos

end Poincare
