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

/-- Every point of a normalized short chord stays within twice the endpoint distance
of its source.  This quantitative estimate is the input used to compare a uniformly
short sphere subpath with its polygonal replacement. -/
theorem dist_normalizedChord_source_le_two_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : dist u v < 2)
    (s : unitInterval) :
    dist ((normalizedChord u v hu hv huv) s : E) u ≤ 2 * dist u v := by
  let c : E := (1 - (s : ℝ)) • u + (s : ℝ) • v
  have hc0 : c ≠ 0 := unit_convexCombo_ne_zero_of_dist_lt_two hu hv huv s
  have huc : dist c u ≤ dist u v := by
    rw [dist_comm, dist_eq_norm]
    have hcsub : u - c = (s : ℝ) • (u - v) := by
      dsimp [c]
      module
    rw [hcsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg s.property.1,
      ← dist_eq_norm]
    exact mul_le_of_le_one_left (dist_nonneg) s.property.2
  have hnorm : |‖c‖ - 1| ≤ dist c u := by
    rw [← hu]
    simpa [dist_eq_norm] using abs_norm_sub_norm_le c u
  have hqc : dist (‖c‖⁻¹ • c) c = |‖c‖ - 1| := by
    rw [dist_eq_norm]
    have hrewrite : ‖c‖⁻¹ • c - c = (‖c‖⁻¹ - 1) • c := by module
    rw [hrewrite, norm_smul, Real.norm_eq_abs]
    have hcnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc0
    have halg : (‖c‖⁻¹ - 1) * ‖c‖ = 1 - ‖c‖ := by
      field_simp
    calc
      |‖c‖⁻¹ - 1| * ‖c‖ = |‖c‖⁻¹ - 1| * |‖c‖| := by
        rw [abs_of_nonneg (norm_nonneg c)]
      _ = |(‖c‖⁻¹ - 1) * ‖c‖| := (abs_mul _ _).symm
      _ = |‖c‖ - 1| := by rw [halg, abs_sub_comm]
  change dist (‖c‖⁻¹ • c) u ≤ 2 * dist u v
  calc
    dist (‖c‖⁻¹ • c) u ≤ dist (‖c‖⁻¹ • c) c + dist c u := dist_triangle _ _ _
    _ ≤ 2 * dist c u := by rw [hqc]; linarith
    _ ≤ 2 * dist u v := by gcongr

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
      (by simp)
      (by simp) (hpq z.2) z.1
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
