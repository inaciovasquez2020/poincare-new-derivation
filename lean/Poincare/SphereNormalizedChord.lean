import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UnitInterval

namespace Poincare

open scoped unitInterval

/-- The straight chord between two unit vectors cannot pass through the origin unless its
endpoints are antipodal. -/
theorem unit_convexCombo_ne_zero_of_dist_lt_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : dist u v < 2) (s : unitInterval) :
    (1 - (s : ℝ)) • u + (s : ℝ) • v ≠ 0 := by
  intro hzero
  have hleft : (1 : ℝ) = (s : ℝ) * dist u v := by
    calc
      (1 : ℝ) = ‖u‖ := hu.symm
      _ = ‖(s : ℝ) • (v - u)‖ := by
        have hrewrite :
            (1 - (s : ℝ)) • u + (s : ℝ) • v = u + (s : ℝ) • (v - u) := by
          module
        rw [hrewrite] at hzero
        have heq : u = -((s : ℝ) • (v - u)) := eq_neg_of_add_eq_zero_left hzero
        calc
          ‖u‖ = ‖-((s : ℝ) • (v - u))‖ := congrArg norm heq
          _ = ‖(s : ℝ) • (v - u)‖ := norm_neg _
      _ = (s : ℝ) * dist u v := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg s.property.1, dist_eq_norm]
        rw [norm_sub_rev]
  have hright : (1 : ℝ) = (1 - (s : ℝ)) * dist u v := by
    calc
      (1 : ℝ) = ‖v‖ := hv.symm
      _ = ‖(1 - (s : ℝ)) • (u - v)‖ := by
        have hrewrite :
            (1 - (s : ℝ)) • u + (s : ℝ) • v =
              v + (1 - (s : ℝ)) • (u - v) := by
          module
        rw [hrewrite] at hzero
        have heq : v = -((1 - (s : ℝ)) • (u - v)) := eq_neg_of_add_eq_zero_left hzero
        calc
          ‖v‖ = ‖-((1 - (s : ℝ)) • (u - v))‖ := congrArg norm heq
          _ = ‖(1 - (s : ℝ)) • (u - v)‖ := norm_neg _
      _ = (1 - (s : ℝ)) * dist u v := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr s.property.2),
          dist_eq_norm]
  have : dist u v = 2 := by linarith
  linarith

end Poincare
