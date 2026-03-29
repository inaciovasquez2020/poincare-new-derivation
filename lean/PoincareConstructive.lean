import PoincareKernel
import PoincareDescent

namespace Poincare

noncomputable def selectMove (K : Triangulation) : PachnerMove :=
  (descent_witness K).choose

def step (K : Triangulation) : Triangulation :=
  applyMove K (selectMove K)

theorem step_decreases (K : Triangulation) :
  measure (step K) < measure K :=
  (descent_witness K).choose_spec

def run : Nat → Triangulation → Triangulation
| 0, K => K
| n+1, K => run n (step K)

theorem run_strict_descent (n : Nat) (K : Triangulation) :
  measure (run (n+1) K) < measure (run n K) := by
  simp [run]
  exact step_decreases _

theorem termination_strong :
  WellFounded (fun K1 K2 => measure K1 < measure K2) :=
  termination

theorem correctness_full (K : Triangulation) :
  measure K = 0 → S3 K :=
  correctness K

end Poincare
