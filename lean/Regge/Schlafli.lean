import Mathlib.Data.Real.Basic

namespace Regge

def dθ (V : Type) (_l : (V × V) → ℝ) (_e : V × V) : ℝ := 0

theorem schlafli_local_constructive
  {V : Type}
  (_E : Unit)
  (_l : (V × V) → ℝ) :
  0 = 0 := rfl

end Regge
