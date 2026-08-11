import Poincare.SphereNormalizedChord
import Mathlib.Topology.UniformSpace.Path

namespace Poincare

open scoped unitInterval

/-- A path admits a positive uniform subdivision count on whose parameter scale its
image has diameter less than `1 / 4`. -/
theorem Path.exists_subdivision_dist_lt_quarter
    {X : Type*} [PseudoMetricSpace X] {x y : X} (p : Path x y) :
    ∃ n : ℕ, 0 < n ∧ ∀ s t : unitInterval,
      dist (s : ℝ) (t : ℝ) ≤ 1 / (n : ℝ) → dist (p s) (p t) < (1 : ℝ) / 4 := by
  obtain ⟨δ, hδ, hp⟩ := Metric.uniformContinuous_iff.mp p.uniformContinuous
    ((1 : ℝ) / 4) (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m + 1, Nat.succ_pos m, fun s t hst ↦ hp ?_⟩
  exact lt_of_le_of_lt hst (by simpa using hm)

end Poincare
