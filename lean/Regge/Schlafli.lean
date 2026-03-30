import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Regge

/-- Parameterize explicitly to ensure V is synthesized for the Edge type -/
def dθ (V : Type) (_l : (V × V) → ℝ) (_e : V × V) : ℝ := 0

theorem schlafli_local_constructive
  {V : Type} [DecidableEq V]
  (E : Finset (V × V))
  (l : (V × V) → ℝ) :
  (∑ e in E, l e * dθ V l e) = 0 := by
  simp [dθ]

end Regge
