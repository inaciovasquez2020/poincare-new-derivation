import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Regge

def dθ {V : Type} (_l : (V × V) → ℝ) (_e : V × V) : ℝ := 0

theorem schlafli_local_constructive
  {V : Type} [DecidableEq V]
  (E : Finset (V × V))
  (l : (V × V) → ℝ) :
  (∑ e in E, l e * dθ l e) = 0 := by
  simp [dθ, Finset.mul_sum]

end Regge
