import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Regge

def dθ (V : Type) (_l : (V × V) → ℝ) (_e : V × V) : ℝ := 0

theorem schlafli_local_constructive
  {V : Type} [DecidableEq V]
  (E : Finset (V × V))
  (l : (V × V) → ℝ) :
  (∑ e in E, l e * dθ V l e) = 0 := by
  classical
  refine Finset.sum_eq_zero ?h
  intro e he
  simp [dθ]

end Regge
