import Poincare.Triangulation
import Poincare.Moves
import Poincare.LocalSphericalDescent

namespace Poincare

def step (T : Triangulation) : Triangulation :=
  applyMove T (selectMove T)

theorem step_strict :
  ∀ T : Triangulation, Phi T > 0 → Phi (step T) < Phi T := by
  intro T hPhi
  obtain ⟨v, hv⟩ := local_positive_vertex_exists T hPhi
  have hstep := local_spherical_descent_step T v hv
  simpa [step]

end Poincare
