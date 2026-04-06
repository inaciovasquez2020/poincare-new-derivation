import Mathlib
import Poincare.Triangulation

namespace Poincare

axiom moveAt : Triangulation → Nat → Triangulation

axiom local_positive_vertex_exists :
  ∀ T : Triangulation,
    Phi T > 0 →
    ∃ v : Nat, vertexDefect T v > 0

axiom local_spherical_descent_step :
  ∀ (T : Triangulation) (v : Nat),
    vertexDefect T v > 0 →
    Phi (moveAt T v) < Phi T

theorem local_spherical_descent_conditional :
  ∀ T,
    Phi T > 0 →
    ∃ T', Phi T' < Phi T := by
  intro T hPhi
  obtain ⟨v, hv⟩ := local_positive_vertex_exists T hPhi
  exact ⟨moveAt T v, local_spherical_descent_step T v hv⟩

end Poincare
