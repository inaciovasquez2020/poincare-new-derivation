import Poincare.SphereNormalizedChord
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.Path

namespace Poincare

open scoped unitInterval

/-- A uniformly short sphere subpath is homotopic, relative to its endpoints, to the
normalized chord joining those endpoints.  The deliberately separated bounds are
the form produced by uniform subdivision and by the normalized-chord estimate. -/
theorem Path.subpath_homotopic_normalizedChord_of_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) (a b : unitInterval)
    (hab : dist (p a : E) (p b : E) < (1 : ℝ) / 4)
    (hsub : ∀ s : unitInterval,
      dist ((p.subpath a b) s : E) (p a : E) < (1 : ℝ) / 2) :
    Path.Homotopic (p.subpath a b)
      (normalizedChord (p a : E) (p b : E)
        (by simpa [Metric.mem_sphere] using (p a).property)
        (by simpa [Metric.mem_sphere] using (p b).property)
        (by linarith)) := by
  let hu : ‖(p a : E)‖ = 1 := by
    simpa [Metric.mem_sphere] using (p a).property
  let hv : ‖(p b : E)‖ = 1 := by
    simpa [Metric.mem_sphere] using (p b).property
  let huv : dist (p a : E) (p b : E) < 2 := by linarith
  apply normalizedStraight_pathHomotopic
  intro s
  calc
    dist ((p.subpath a b) s : E)
        ((normalizedChord (p a : E) (p b : E) hu hv huv) s : E) ≤
        dist ((p.subpath a b) s : E) (p a : E) +
          dist (p a : E)
            ((normalizedChord (p a : E) (p b : E) hu hv huv) s : E) :=
      dist_triangle _ _ _
    _ < 2 := by
      rw [dist_comm (p a : E)]
      have hchord := dist_normalizedChord_source_le_two_mul hu hv huv s
      have hs := hsub s
      linarith

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

/-- A sphere-valued path has uniformly short sampled edges whose normalized chord
stays within `1 / 2` of the source vertex.  This is the quantitative local input for
homotoping each sampled subpath to its polygonal replacement. -/
theorem Path.exists_sampled_sphere_vertices_normalizedChord_close
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p : Path x y) :
    ∃ n : ℕ, 0 < n ∧ ∃ v : Fin (n + 1) → unitInterval,
      v 0 = 0 ∧ v (Fin.last n) = 1 ∧
        ∀ i : Fin n,
          dist (p (v i.castSucc) : E) (p (v i.succ) : E) < (1 : ℝ) / 4 ∧
          ∃ huv : dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2,
            ∀ s : unitInterval,
              dist
                  ((normalizedChord
                    (p (v i.castSucc) : E) (p (v i.succ) : E)
                    (by simpa [Metric.mem_sphere] using (p (v i.castSucc)).property)
                    (by simpa [Metric.mem_sphere] using (p (v i.succ)).property)
                    huv) s : E)
                  (p (v i.castSucc) : E) < (1 : ℝ) / 2 := by
  obtain ⟨n, hn, v, hv0, hv1, hv⟩ := Path.exists_sampled_vertices_dist_lt_quarter p
  have hedge (i : Fin n) :
      dist (p (v i.castSucc) : E) (p (v i.succ) : E) < (1 : ℝ) / 4 := by
    simpa [Subtype.dist_eq] using hv i
  refine ⟨n, hn, v, hv0, hv1, fun i ↦ ⟨hedge i, ?_⟩⟩
  have hu : ‖(p (v i.castSucc) : E)‖ = 1 := by
    simpa [Metric.mem_sphere] using (p (v i.castSucc)).property
  have hw : ‖(p (v i.succ) : E)‖ = 1 := by
    simpa [Metric.mem_sphere] using (p (v i.succ)).property
  have huv : dist (p (v i.castSucc) : E) (p (v i.succ) : E) < 2 := by
    linarith [hedge i]
  refine ⟨huv, fun s ↦ ?_⟩
  exact lt_of_le_of_lt
    (dist_normalizedChord_source_le_two_mul hu hw huv s) (by linarith [hedge i])

end Poincare
