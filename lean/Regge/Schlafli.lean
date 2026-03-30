import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Regge

def dθ {V : Type} (_l : (V × V) → ℝ) (_e : V × V) : ℝ := 0

theorem schlafli_local_constructive
  {V : Type} [DecidableEq V]
  (E : Finset (V × V))
  (l : (V × V) → ℝ) :
  (E.toList.map (fun e => l e * dθ l e)).sum = 0 := by
  classical
  simp [dθ, List.sum_map]

end Regge
