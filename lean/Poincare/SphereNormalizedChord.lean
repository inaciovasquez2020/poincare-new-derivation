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

end Poincare
