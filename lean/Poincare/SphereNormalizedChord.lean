import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homotopy.Path
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

/-- The short normalized chord between two points of a unit sphere, as a sphere-valued path. -/
noncomputable def normalizedChord
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : dist u v < 2) :
    Path (⟨u, by simpa [Metric.mem_sphere] using hu⟩ : Metric.sphere (0 : E) 1)
      ⟨v, by simpa [Metric.mem_sphere] using hv⟩ := by
  let c : unitInterval → E := fun s ↦ (1 - (s : ℝ)) • u + (s : ℝ) • v
  have hc0 : ∀ s, c s ≠ 0 := fun s ↦
    unit_convexCombo_ne_zero_of_dist_lt_two hu hv huv s
  let f : unitInterval → Metric.sphere (0 : E) 1 := fun s ↦
    ⟨‖c s‖⁻¹ • c s, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hc0 s))]⟩
  have hc : Continuous c :=
    (continuous_const.sub continuous_subtype_val).smul continuous_const |>.add
      (continuous_subtype_val.smul continuous_const)
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact (hc.norm.inv₀ (fun s ↦ norm_ne_zero_iff.mpr (hc0 s))).smul hc
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · apply Subtype.ext
    simp [f, c, hu]
  · apply Subtype.ext
    simp [f, c, hv]

/-- A short pair of unit vectors is joined on the unit sphere by its normalized straight chord. -/
theorem exists_normalizedChord_path
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : dist u v < 2) :
    ∃ p : Path (⟨u, by simpa [Metric.mem_sphere] using hu⟩ : Metric.sphere (0 : E) 1)
        ⟨v, by simpa [Metric.mem_sphere] using hv⟩,
      ∀ s, (p s : E) = ‖(1 - (s : ℝ)) • u + (s : ℝ) • v‖⁻¹ •
        ((1 - (s : ℝ)) • u + (s : ℝ) • v) := by
  refine ⟨normalizedChord u v hu hv huv, ?_⟩
  intro s
  simp [normalizedChord]

/-- Sphere-valued paths which are pointwise less than two apart are homotopic through
pointwise normalized straight chords. -/
theorem normalizedStraight_pathHomotopic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : Metric.sphere (0 : E) 1} (p q : Path x y)
    (hpq : ∀ t, dist (p t : E) (q t : E) < 2) :
    Path.Homotopic p q := by
  let c : unitInterval × unitInterval → E := fun z ↦
    (1 - (z.1 : ℝ)) • (p z.2 : E) + (z.1 : ℝ) • (q z.2 : E)
  have hc0 : ∀ z, c z ≠ 0 := fun z ↦
    unit_convexCombo_ne_zero_of_dist_lt_two
      (by simpa [Metric.mem_sphere] using (p z.2).property)
      (by simpa [Metric.mem_sphere] using (q z.2).property) (hpq z.2) z.1
  have hc : Continuous c :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (p.continuous.subtype_val.comp continuous_snd) |>.add
      ((continuous_subtype_val.comp continuous_fst).smul
        (q.continuous.subtype_val.comp continuous_snd))
  let f : unitInterval × unitInterval → Metric.sphere (0 : E) 1 := fun z ↦
    ⟨‖c z‖⁻¹ • c z, by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hc0 z))]⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact (hc.norm.inv₀ (fun z ↦ norm_ne_zero_iff.mpr (hc0 z))).smul hc
  refine ⟨{
    toFun := f
    continuous_toFun := hf
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    apply Subtype.ext
    simp [f, c]
  · intro t
    apply Subtype.ext
    simp [f, c]
  · intro s t ht
    rcases ht with rfl | rfl
    · change f (s, 0) = p 0
      rw [p.source]
      apply Subtype.ext
      simp only [f, c]
      rw [p.source, q.source]
      have hcombo : (1 - (s : ℝ)) • (x : E) + (s : ℝ) • (x : E) = x := by
        module
      rw [hcombo]
      simp
    · change f (s, 1) = p 1
      rw [p.target]
      apply Subtype.ext
      simp only [f, c]
      rw [p.target, q.target]
      have hcombo : (1 - (s : ℝ)) • (y : E) + (s : ℝ) • (y : E) = y := by
        module
      rw [hcombo]
      simp

end Poincare
