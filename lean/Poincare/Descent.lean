import Poincare.Kernel

namespace Poincare

def step (K : Triangulation) (h : K.complexity > 0) : Triangulation :=
  applyMove K (selectMove K)

theorem step_decreases (K : Triangulation) (h : K.complexity > 0) :
  measure (step K h) < measure K :=
  descent_witness K h

def run : Nat → Triangulation → Triangulation
| 0, K => K
| n+1, K =>
    if h : K.complexity > 0 then run n (step K h) else K

end Poincare
