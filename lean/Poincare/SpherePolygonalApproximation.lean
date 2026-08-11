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

/-- A path has a finite sequence of equally spaced sampled vertices whose consecutive
vertices are less than `1 / 4` apart. -/
theorem Path.exists_sampled_vertices_dist_lt_quarter
    {X : Type*} [PseudoMetricSpace X] {x y : X} (p : Path x y) :
    ∃ n : ℕ, 0 < n ∧ ∃ v : Fin (n + 1) → unitInterval,
      v 0 = 0 ∧ v (Fin.last n) = 1 ∧
        ∀ i : Fin n, dist (p (v i.castSucc)) (p (v i.succ)) < (1 : ℝ) / 4 := by
  obtain ⟨n, hn, hp⟩ := Path.exists_subdivision_dist_lt_quarter p
  let v : Fin (n + 1) → unitInterval := fun i ↦
    ⟨(i : ℝ) / n, by
      constructor
      · positivity
      · rw [div_le_one (by exact_mod_cast hn)]
        have hi : (i : ℕ) ≤ n := by omega
        exact_mod_cast hi⟩
  refine ⟨n, hn, v, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp [v]
  · apply Subtype.ext
    simp [v, hn.ne']
  · intro i
    apply hp
    rw [Real.dist_eq]
    simp only [v]
    rw [show ((i.succ : Fin (n + 1)) : ℝ) = (i : ℝ) + 1 by norm_num,
      add_div, one_div]
    simp

end Poincare
