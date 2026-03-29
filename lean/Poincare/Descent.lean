import Poincare.Moves

namespace Poincare

def step (K : Triangulation) : Triangulation :=
  applyMove K (selectMove K)

def run : Nat → Triangulation → Triangulation
| 0, K => K
| n+1, K => run n (step K)

axiom local_defect_strict_descent :
  ∀ K, Phi K > 0 → Phi (step K) = Phi K - 1

theorem step_decreases (K : Triangulation) (h : Phi K > 0) :
    Phi (step K) < Phi K := by
  rw [local_defect_strict_descent K h]
  omega

end Poincare
