import Poincare.Kernel

namespace Poincare

noncomputable def stepMove (K : Triangulation) (h : K.complexity > 0) : PachnerMove :=
  Classical.choose (descent_witness K h)

noncomputable def step (K : Triangulation) (h : K.complexity > 0) : Triangulation :=
  applyMove K (stepMove K h)

theorem step_decreases (K : Triangulation) (h : K.complexity > 0) :
    measure (step K h) < measure K :=
  Classical.choose_spec (descent_witness K h)

noncomputable def run : Nat → Triangulation → Triangulation
  | 0,   K => K
  | n+1, K => if h : K.complexity > 0 then run n (step K h) else K

end Poincare
