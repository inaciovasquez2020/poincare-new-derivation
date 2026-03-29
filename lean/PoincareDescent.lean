import PoincareKernel

namespace Poincare

def step (K : Triangulation) : Triangulation :=
  Classical.choose (descent_witness K)

theorem step_decreases (K : Triangulation) :
  measure (step K) < measure K :=
  (Classical.choose_spec (descent_witness K))

def run : Nat → Triangulation → Triangulation
| 0, K => K
| n+1, K => run n (step K)

theorem run_decreases (n : Nat) (K : Triangulation) :
  measure (run (n+1) K) < measure (run n K) := by
  simp [run]
  apply step_decreases

end Poincare
