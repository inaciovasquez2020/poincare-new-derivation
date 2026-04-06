import Mathlib
import Poincare.Triangulation
import Poincare.Moves
import Poincare.ExistsStrictDescentMove

namespace Poincare

noncomputable def solveStep (K : Triangulation) : Triangulation :=
  if h : Phi K = 0 then
    K
  else
    applyMove K (Classical.choose (exists_strict_descent_move K h))

theorem solveStep_fixed_on_zero :
  ∀ K : Triangulation, Phi K = 0 → solveStep K = K := by
  intro K h0
  simp [solveStep, h0]

theorem solveStep_strict_descent :
  ∀ K : Triangulation, Phi K > 0 → Phi (solveStep K) < Phi K := by
  intro K hpos
  have hne : Phi K ≠ 0 := Nat.ne_of_gt hpos
  have hchoose :
      Phi (applyMove K (Classical.choose (exists_strict_descent_move K hne))) < Phi K := by
    exact (Classical.choose_spec (exists_strict_descent_move K hne))
  simpa [solveStep, hne] using hchoose

theorem solveStep_nonincreasing :
  ∀ K : Triangulation, Phi (solveStep K) ≤ Phi K := by
  intro K
  by_cases h0 : Phi K = 0
  · simp [solveStep, h0]
  · have hpos : Phi K > 0 := Nat.pos_of_ne_zero h0
    exact Nat.le_of_lt (solveStep_strict_descent K hpos)

theorem solveStep_preserves_zero :
  ∀ K : Triangulation, Phi K = 0 → Phi (solveStep K) = 0 := by
  intro K h0
  simp [solveStep, h0]

theorem original_solve_realized :
  ∀ K : Triangulation, Phi K > 0 → Phi (solveStep K) < Phi K := by
  exact solveStep_strict_descent

theorem original_solve_test_passes :
  ¬ ∃ K : Triangulation, Phi K > 0 ∧ ¬ Phi (solveStep K) < Phi K := by
  intro h
  rcases h with ⟨K, hpos, hfail⟩
  exact hfail (solveStep_strict_descent K hpos)

theorem original_solve_zero_case :
  ∀ K : Triangulation, Phi K = 0 → solveStep K = K := by
  exact solveStep_fixed_on_zero

end Poincare
