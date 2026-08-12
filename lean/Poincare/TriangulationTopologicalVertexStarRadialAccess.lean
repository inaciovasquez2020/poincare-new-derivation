import Poincare.TriangulationTopologicalVertexStarNeighborhood
import Poincare.TriangulationTopologicalVertexLinkRealizationChange
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter

namespace Poincare

/-- The represented vertex star is contained in the full geometric realization. -/
theorem triangulationTopologicalVertexStar_subset_space
    (K : Triangulation) (v : Nat) :
    triangulationTopologicalVertexStar K v ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  intro p hp
  obtain ⟨tau, htau, _, hpbody⟩ :=
    (mem_triangulationTopologicalVertexStar_iff K v p).1 hp
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  simp only [mem_iUnion]
  exact ⟨tau, htau, hpbody⟩

/-- A non-apex point on the radial segment from a represented vertex to a
represented link point, regarded as a point of the full carrier. -/
noncomputable def triangulationTopologicalRadialCarrierPoint
    (K : Triangulation) (v : Nat)
    (t : ↥(Set.Ico (0 : ℝ) 1))
    (q : ↥(triangulationTopologicalVertexLink K v)) :
    triangulationTopologicalGeometricCarrier K :=
  ⟨t.1 • triangulationTopologicalGeometricVertex v + (1 - t.1) • q.1,
    triangulationTopologicalVertexStar_subset_space K v
      (triangulationTopologicalVertexStar_radial_mem
        K v q.1 q.2 t.1 t.2.1 t.2.2)⟩

@[simp] theorem triangulationTopologicalRadialCarrierPoint_val
    (K : Triangulation) (v : Nat)
    (t : ↥(Set.Ico (0 : ℝ) 1))
    (q : ↥(triangulationTopologicalVertexLink K v)) :
    (triangulationTopologicalRadialCarrierPoint K v t q).1 =
      t.1 • triangulationTopologicalGeometricVertex v + (1 - t.1) • q.1 := rfl

@[simp] theorem triangulationTopologicalRadialCarrierPoint_coordinate
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    (v : Nat) (t : ↥(Set.Ico (0 : ℝ) 1))
    (q : ↥(triangulationTopologicalVertexLink K v)) :
    (triangulationTopologicalRadialCarrierPoint K v t q).1 v = t.1 := by
  simp [triangulationTopologicalRadialCarrierPoint,
    triangulationTopologicalGeometricVertex,
    triangulationTopologicalVertexLink_apex_coordinate_eq_zero
      K hcore v q.1 q.2]

theorem triangulationTopologicalRadialCarrierPoint_ne_carrierVertex
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v : Nat} (hv : v ∈ vertexSupport K)
    (t : ↥(Set.Ico (0 : ℝ) 1))
    (q : ↥(triangulationTopologicalVertexLink K v)) :
    triangulationTopologicalRadialCarrierPoint K v t q ≠
      triangulationTopologicalCarrierVertex K v hv := by
  intro h
  have hcoord := congrArg (fun p : triangulationTopologicalGeometricCarrier K ↦ p.1 v) h
  change (triangulationTopologicalRadialCarrierPoint K v t q).1 v =
    (triangulationTopologicalCarrierVertex K v hv).1 v at hcoord
  rw [triangulationTopologicalRadialCarrierPoint_coordinate K hcore,
    triangulationTopologicalCarrierVertex_coordinate] at hcoord
  exact (ne_of_lt t.2.2) hcoord

/-- Explicit parameters in `[0,1)` approaching the apex parameter `1`. -/
noncomputable def triangulationTopologicalRadialApproachParameter
    (n : Nat) : ↥(Set.Ico (0 : ℝ) 1) :=
  ⟨1 - 1 / ((n : ℝ) + 1), by
    constructor
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := by
        exact (div_le_one (by positivity)).2 hn
      linarith
    · have hdiv : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith⟩

theorem tendsto_triangulationTopologicalRadialApproachParameter :
    Tendsto
      (fun n : Nat ↦ (triangulationTopologicalRadialApproachParameter n).1)
      atTop (nhds 1) := by
  simpa [triangulationTopologicalRadialApproachParameter] using
    (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun n : Nat ↦ 1 - 1 / ((n : ℝ) + 1)) atTop (nhds (1 - 0)))

/-- Along every represented link direction, the explicit radial carrier points
converge to the represented carrier vertex. -/
theorem tendsto_triangulationTopologicalRadialCarrierPoint_carrierVertex
    (K : Triangulation) (_hcore : ClosedTriangulationCore K)
    {v : Nat} (hv : v ∈ vertexSupport K)
    (q : ↥(triangulationTopologicalVertexLink K v)) :
    Tendsto
      (fun n : Nat ↦
        triangulationTopologicalRadialCarrierPoint K v
          (triangulationTopologicalRadialApproachParameter n) q)
      atTop
      (nhds (triangulationTopologicalCarrierVertex K v hv)) := by
  apply tendsto_subtype_rng.mpr
  have ht := tendsto_triangulationTopologicalRadialApproachParameter
  have hcoeff : Tendsto
      (fun n : Nat ↦ (1 : ℝ) -
        (triangulationTopologicalRadialApproachParameter n).1)
      atTop (nhds ((1 : ℝ) - 1)) :=
    tendsto_const_nhds.sub ht
  have hambient : Tendsto
      (fun n : Nat ↦
        (triangulationTopologicalRadialApproachParameter n).1 •
            triangulationTopologicalGeometricVertex v +
          (1 - (triangulationTopologicalRadialApproachParameter n).1) • q.1)
      atTop
      (nhds ((1 : ℝ) • triangulationTopologicalGeometricVertex v +
        ((1 : ℝ) - 1) • q.1)) :=
    (ht.smul_const (triangulationTopologicalGeometricVertex v)).add
      (hcoeff.smul_const q.1)
  simpa [triangulationTopologicalRadialCarrierPoint,
    triangulationTopologicalCarrierVertex] using hambient

/-- Every carrier neighborhood of the represented apex meets every individual
radial ray through a represented link point. -/
theorem triangulationTopological_exists_radialCarrierPoint_mem_of_mem_nhds
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v : Nat} (hv : v ∈ vertexSupport K)
    (q : ↥(triangulationTopologicalVertexLink K v))
    {U : Set (triangulationTopologicalGeometricCarrier K)}
    (hU : U ∈ nhds (triangulationTopologicalCarrierVertex K v hv)) :
    ∃ t : ↥(Set.Ico (0 : ℝ) 1),
      triangulationTopologicalRadialCarrierPoint K v t q ∈ U := by
  have heventually :=
    (tendsto_triangulationTopologicalRadialCarrierPoint_carrierVertex
      K hcore hv q) hU
  obtain ⟨N, hN⟩ := (eventually_atTop.1 heventually)
  exact ⟨triangulationTopologicalRadialApproachParameter N, hN N le_rfl⟩

/-- Open-set wrapper for radial access at a represented apex. -/
theorem triangulationTopological_open_mem_apex_intersects_radialRay
    (K : Triangulation) (hcore : ClosedTriangulationCore K)
    {v : Nat} (hv : v ∈ vertexSupport K)
    (q : ↥(triangulationTopologicalVertexLink K v))
    {U : Set (triangulationTopologicalGeometricCarrier K)}
    (hUopen : IsOpen U)
    (hapex : triangulationTopologicalCarrierVertex K v hv ∈ U) :
    ∃ t : ↥(Set.Ico (0 : ℝ) 1),
      triangulationTopologicalRadialCarrierPoint K v t q ∈ U := by
  exact triangulationTopological_exists_radialCarrierPoint_mem_of_mem_nhds
    K hcore hv q (hUopen.mem_nhds hapex)

end Poincare

namespace Poincare

/--
The closed radial cone family, including the apex parameter `t = 1`.

For `t < 1` this is the existing represented radial star point.
At `t = 1` the expression collapses to the represented carrier vertex.
-/
noncomputable def triangulationTopologicalClosedRadialCarrierPoint
    (K : Triangulation)
    (v : Nat)
    (hv : v ∈ vertexSupport K)
    (t : ↥(Set.Icc (0 : ℝ) 1))
    (q : ↥(triangulationTopologicalVertexLink K v)) :
    triangulationTopologicalGeometricCarrier K :=
  ⟨
    t.1 • triangulationTopologicalGeometricVertex v +
      (1 - t.1) • q.1,
    by
      by_cases ht : t.1 < 1
      · exact
          triangulationTopologicalVertexStar_subset_space K v
            (triangulationTopologicalVertexStar_radial_mem
              K v q.1 q.2 t.1 t.2.1 ht)
      · have ht_ge : (1 : ℝ) ≤ t.1 := le_of_not_gt ht
        have ht_eq : t.1 = 1 := le_antisymm t.2.2 ht_ge
        simpa [
          ht_eq,
          triangulationTopologicalCarrierVertex
        ] using
          (triangulationTopologicalCarrierVertex K v hv).2
  ⟩

/--
The closed radial family is jointly continuous in the radial parameter
and the represented vertex-link point.
-/
theorem continuous_triangulationTopologicalClosedRadialCarrierPoint
    (K : Triangulation)
    (v : Nat)
    (hv : v ∈ vertexSupport K) :
    Continuous
      (fun tq :
        ↥(Set.Icc (0 : ℝ) 1) ×
          ↥(triangulationTopologicalVertexLink K v) =>
        triangulationTopologicalClosedRadialCarrierPoint
          K v hv tq.1 tq.2) := by
  apply Continuous.subtype_mk
  exact
    ((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
      ((continuous_const.sub
          (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd))

/-- The endpoint parameter of the closed radial cone. -/
noncomputable def triangulationTopologicalClosedRadialOne :
    ↥(Set.Icc (0 : ℝ) 1) :=
  ⟨1, by constructor <;> norm_num⟩

@[simp]
theorem triangulationTopologicalClosedRadialCarrierPoint_one
    (K : Triangulation)
    (v : Nat)
    (hv : v ∈ vertexSupport K)
    (q : ↥(triangulationTopologicalVertexLink K v)) :
    triangulationTopologicalClosedRadialCarrierPoint
        K v hv triangulationTopologicalClosedRadialOne q =
      triangulationTopologicalCarrierVertex K v hv := by
  apply Subtype.ext
  simp [
    triangulationTopologicalClosedRadialCarrierPoint,
    triangulationTopologicalClosedRadialOne,
    triangulationTopologicalCarrierVertex
  ]

/--
Compactness upgrades pointwise radial approach to a parameter
neighborhood that works simultaneously for every point of the
represented vertex link.
-/
theorem eventually_triangulationTopologicalClosedRadialCarrierPoint_mem_of_mem_nhds
    (K : Triangulation)
    {v : Nat}
    (hv : v ∈ vertexSupport K)
    (U : Set (triangulationTopologicalGeometricCarrier K))
    (hU :
      U ∈ nhds (triangulationTopologicalCarrierVertex K v hv)) :
    ∀ᶠ t in nhds triangulationTopologicalClosedRadialOne,
      ∀ q : ↥(triangulationTopologicalVertexLink K v),
        triangulationTopologicalClosedRadialCarrierPoint
          K v hv t q ∈ U := by
  letI : CompactSpace
      ↥(triangulationTopologicalVertexLink K v) :=
    isCompact_iff_compactSpace.mp
      (triangulationTopologicalVertexLink_isCompact K v)

  have hpoint :
      ∀ q : ↥(triangulationTopologicalVertexLink K v),
        ∀ᶠ tq :
            ↥(Set.Icc (0 : ℝ) 1) ×
              ↥(triangulationTopologicalVertexLink K v)
          in nhds (triangulationTopologicalClosedRadialOne, q),
          triangulationTopologicalClosedRadialCarrierPoint
            K v hv tq.1 tq.2 ∈ U := by
    intro q

    have hU' :
        U ∈ nhds
          (triangulationTopologicalClosedRadialCarrierPoint
            K v hv triangulationTopologicalClosedRadialOne q) := by
      simpa using hU

    exact
      (continuous_triangulationTopologicalClosedRadialCarrierPoint
        K v hv).continuousAt.eventually hU'

  simpa only [Set.mem_univ, forall_const] using
    (isCompact_univ.eventually_forall_of_forall_eventually
      (K :=
        (Set.univ :
          Set ↥(triangulationTopologicalVertexLink K v)))
      (x₀ := triangulationTopologicalClosedRadialOne)
      (P := fun t q =>
        triangulationTopologicalClosedRadialCarrierPoint
          K v hv t q ∈ U)
      (fun q _ => hpoint q))

/--
The existing explicit radial approach parameter, regarded in the
closed interval `[0,1]`.
-/
noncomputable def triangulationTopologicalClosedRadialApproachParameter
    (n : Nat) :
    ↥(Set.Icc (0 : ℝ) 1) :=
  ⟨
    (triangulationTopologicalRadialApproachParameter n).1,
    (triangulationTopologicalRadialApproachParameter n).2.1,
    le_of_lt
      (triangulationTopologicalRadialApproachParameter n).2.2
  ⟩

theorem tendsto_triangulationTopologicalClosedRadialApproachParameter :
    Tendsto
      triangulationTopologicalClosedRadialApproachParameter
      atTop
      (nhds triangulationTopologicalClosedRadialOne) := by
  apply tendsto_subtype_rng.mpr
  simpa [
    triangulationTopologicalClosedRadialApproachParameter,
    triangulationTopologicalClosedRadialOne
  ] using
    tendsto_triangulationTopologicalRadialApproachParameter

@[simp]
theorem triangulationTopologicalClosedRadialCarrierPoint_approach
    (K : Triangulation)
    (v : Nat)
    (hv : v ∈ vertexSupport K)
    (n : Nat)
    (q : ↥(triangulationTopologicalVertexLink K v)) :
    triangulationTopologicalClosedRadialCarrierPoint
        K v hv
        (triangulationTopologicalClosedRadialApproachParameter n)
        q =
      triangulationTopologicalRadialCarrierPoint
        K v
        (triangulationTopologicalRadialApproachParameter n)
        q := by
  apply Subtype.ext
  rfl

/--
Uniform radial-slice theorem.

Every carrier neighborhood of a represented apex contains one complete
radial copy of the entire represented vertex link at a single explicit
approach parameter.
-/
theorem triangulationTopological_exists_uniform_radialCarrierPoint_mem_of_mem_nhds
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    {v : Nat}
    (hv : v ∈ vertexSupport K)
    {U : Set (triangulationTopologicalGeometricCarrier K)}
    (hU :
      U ∈ nhds (triangulationTopologicalCarrierVertex K v hv)) :
    ∃ n : Nat,
      ∀ q : ↥(triangulationTopologicalVertexLink K v),
        triangulationTopologicalRadialCarrierPoint
          K v
          (triangulationTopologicalRadialApproachParameter n)
          q ∈ U := by
  have hclosed :=
    eventually_triangulationTopologicalClosedRadialCarrierPoint_mem_of_mem_nhds
      K hv U hU

  have hseq :
      ∀ᶠ n : Nat in atTop,
        ∀ q : ↥(triangulationTopologicalVertexLink K v),
          triangulationTopologicalClosedRadialCarrierPoint
            K v hv
            (triangulationTopologicalClosedRadialApproachParameter n)
            q ∈ U :=
    tendsto_triangulationTopologicalClosedRadialApproachParameter hclosed

  obtain ⟨N, hN⟩ := eventually_atTop.1 hseq

  refine ⟨N, ?_⟩
  intro q

  have h :=
    hN N le_rfl q

  simpa only [
    triangulationTopologicalClosedRadialCarrierPoint_approach
  ] using h

end Poincare
