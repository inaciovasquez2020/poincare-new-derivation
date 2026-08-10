import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set

namespace Poincare

/-- The Euclidean three-space used for the triangular-bipyramid model. -/
abbrev Move23BipyramidAmbient :=
  EuclideanSpace ℝ (Fin 3)

/--
Membership in the convex hull of four labelled points is exactly presentation
as a convex combination whose coefficients retain those labels.
-/
theorem mem_convexHull_range_fin4_iff_exists_weights
    (v : Fin 4 → Move23BipyramidAmbient) (x : Move23BipyramidAmbient) :
    x ∈ convexHull ℝ (Set.range v) ↔
      ∃ w : Fin 4 → ℝ,
        (∀ i, 0 ≤ w i) ∧
        (∑ i, w i = 1) ∧
        ∑ i, w i • v i = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_range_eq_exists_affineCombination] at hx
    obtain ⟨s, a, ha_nonneg, ha_sum, ha_comb⟩ := hx
    let w : Fin 4 → ℝ := fun i => if i ∈ s then a i else 0
    refine ⟨w, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ s
      · simpa [w, hi] using ha_nonneg i hi
      · simp [w, hi]
    · simpa [w] using ha_sum
    · rw [← ha_comb]
      rw [Finset.affineCombination_eq_linear_combination s v a ha_sum]
      simp [w]
  · rintro ⟨w, hw_nonneg, hw_sum, rfl⟩
    exact mem_convexHull_of_exists_fintype w v hw_nonneg hw_sum
      (fun i => Set.mem_range_self i) rfl

end Poincare
