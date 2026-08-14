import Poincare.GlobalMove32ReentryPolygonalLoop
import Poincare.CarrierPositiveCoordinateCover
import Mathlib.Algebra.Order.Floor.Semiring

namespace Poincare

/-- Simple connectivity supplies the full relative null-homotopy square for
the recurrence-driven polygonal loop.  In particular, this theorem applies
to the new ordered loop, not to `crossingPath.trans crossingPath.symm`. -/
theorem WitnessedReentryPolygonalLoopCertificate.exists_nullHomotopyData
    {K : Triangulation} (hSC : TriangulationRealizationSimplyConnected K)
    (c : WitnessedReentryPolygonalLoopCertificate K) :
    Nonempty (CarrierLoopNullHomotopyData K c.basepoint c.polygonalLoop) := by
  exact exists_carrierLoopNullHomotopyData hSC c.polygonalLoop

/-- The recurrent combinatorial certificate, its ordered polygonal loop, and
all four exact boundary equations of a relative null-homotopy can be chosen
simultaneously. -/
theorem ClosedTriangulationCore.exists_polygonalLoop_nullHomotopyData_of_witnessedReentry_recurrent_crossing
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hSC : TriangulationRealizationSimplyConnected K)
    (c : WitnessedReentryCrossingCertificate K)
    (hrealized : ∀ n, (c.sites n).RealizedIn K)
    (hthree : ∀ n, (c.sites n).SharedEdgeExactlyThree K)
    (hwitnessed : ∀ n,
      Move32SourceFaceWitnessedReentry K (c.sites n) (c.sites (n + 1))) :
    ∃ p : WitnessedReentryPolygonalLoopCertificate K,
      Nonempty (CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop) := by
  let p := (hcore.exists_polygonalLoopCertificate_of_witnessedReentry_recurrent_crossing
    c hrealized hthree hwitnessed).some
  exact ⟨p, p.exists_nullHomotopyData hSC⟩

/- Certified finite square-grid and dyadic-refinement layer, integrated 2026-08-14. -/
namespace CarrierLoopNullHomotopyData

/--
For one fixed carrier coordinate of a relative null-homotopy square, there is
a uniform positive subdivision scale such that a coordinate which is at least
`1 / 4` at one parameter point remains strictly positive at every parameter
point within one subdivision diameter.

This is the analytic cell-control input for the later finite square
subdivision; it introduces no cell structure yet.
-/
theorem exists_uniform_coordinate_positive_scale_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (v : Nat) :
    ∃ n : Nat, 0 < n ∧
      ∀ z w : unitInterval × unitInterval,
        dist z w ≤ 1 / (n : ℝ) →
        (1 : ℝ) / 4 ≤ (H.homotopy z).1 v →
        0 < (H.homotopy w).1 v := by
  have hcontinuous :
      Continuous
        (fun z : unitInterval × unitInterval =>
          (H.homotopy z).1 v) := by
    exact
      (continuous_apply v).comp
        (continuous_subtype_val.comp H.homotopy.continuous)

  have huniform :
      UniformContinuous
        (fun z : unitInterval × unitInterval =>
          (H.homotopy z).1 v) :=
    CompactSpace.uniformContinuous_of_continuous hcontinuous

  obtain ⟨δ, hδ, hcontrol⟩ :=
    Metric.uniformContinuous_iff.mp huniform
      ((1 : ℝ) / 8) (by norm_num)

  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ

  refine ⟨m + 1, Nat.succ_pos m, ?_⟩

  intro z w hzw hzquarter

  have hparam : dist z w < δ := by
    exact lt_of_le_of_lt hzw (by simpa using hm)

  have hcoord :
      dist ((H.homotopy z).1 v) ((H.homotopy w).1 v) <
        (1 : ℝ) / 8 :=
    hcontrol hparam

  rw [Real.dist_eq] at hcoord
  have hbounds := abs_lt.mp hcoord
  linarith



/--
The finitely many represented carrier coordinates admit one common
subdivision count.  Any supported coordinate which is at least `1 / 4`
at one parameter point remains strictly positive throughout one
common-scale parameter neighborhood.
-/
theorem exists_uniform_vertexSupport_coordinate_positive_scale_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop) :
    ∃ N : Nat, 0 < N ∧
      ∀ v ∈ vertexSupport K,
        ∀ z w : unitInterval × unitInterval,
          dist z w ≤ 1 / (N : ℝ) →
          (1 : ℝ) / 4 ≤ (H.homotopy z).1 v →
          0 < (H.homotopy w).1 v := by
  classical

  let S : Finset Nat := (vertexSupport K).toFinset

  have hscale :
      ∀ v : Nat,
        ∃ n : Nat, 0 < n ∧
          ∀ z w : unitInterval × unitInterval,
            dist z w ≤ 1 / (n : ℝ) →
            (1 : ℝ) / 4 ≤ (H.homotopy z).1 v →
            0 < (H.homotopy w).1 v := by
    intro v
    exact H.exists_uniform_coordinate_positive_scale_probe v

  choose n hn using hscale

  let N : Nat := S.sup n + 1

  refine ⟨N, by
    dsimp [N]
    exact Nat.succ_pos _, ?_⟩

  intro v hvSupport z w hzw hzquarter

  have hvS : v ∈ S := by
    simpa [S] using (List.mem_toFinset.mpr hvSupport)

  have hnvSup : n v ≤ S.sup n := by
    exact Finset.le_sup hvS

  have hnvN : n v ≤ N := by
    dsimp [N]
    omega

  have hnvPos : 0 < n v :=
    (hn v).1

  have hrecip :
      1 / (N : ℝ) ≤ 1 / (n v : ℝ) := by
    apply one_div_le_one_div_of_le
    · exact_mod_cast hnvPos
    · exact_mod_cast hnvN

  exact (hn v).2 z w (hzw.trans hrecip) hzquarter



/-- The standard equally-spaced parameter point `i / N`. -/
noncomputable def squareGridParameter
    (N : Nat) (hN : 0 < N) (i : Fin (N + 1)) :
    unitInterval :=
  ⟨(i : ℝ) / N, by
    constructor
    · positivity
    · rw [div_le_one (by exact_mod_cast hN)]
      have hi : (i : Nat) ≤ N := by
        omega
      exact_mod_cast hi⟩

/-- One closed cell of the standard `N × N` subdivision of the parameter square. -/
def squareGridCell
    (N : Nat) (hN : 0 < N) (i j : Fin N) :
    Set (unitInterval × unitInterval) :=
  {z |
    (squareGridParameter N hN i.castSucc : ℝ) ≤ (z.1 : ℝ) ∧
    (z.1 : ℝ) ≤ (squareGridParameter N hN i.succ : ℝ) ∧
    (squareGridParameter N hN j.castSucc : ℝ) ≤ (z.2 : ℝ) ∧
    (z.2 : ℝ) ≤ (squareGridParameter N hN j.succ : ℝ)}

/-- The southwest corner of a standard square-grid cell. -/
noncomputable def squareGridCellSource
    (N : Nat) (hN : 0 < N) (i j : Fin N) :
    unitInterval × unitInterval :=
  (squareGridParameter N hN i.castSucc,
    squareGridParameter N hN j.castSucc)

/--
Every point of a standard grid cell is within parameter distance `1 / N`
of its southwest corner.
-/
theorem squareGridCell_dist_source_le
    (N : Nat) (hN : 0 < N) (i j : Fin N)
    {z : unitInterval × unitInterval}
    (hz : z ∈ squareGridCell N hN i j) :
    dist (squareGridCellSource N hN i j) z ≤ 1 / (N : ℝ) := by
  rcases hz with ⟨hxi0, hxi1, hyj0, hyj1⟩
  rw [Prod.dist_eq, max_le_iff]
  constructor
  · rw [Subtype.dist_eq, Real.dist_eq]
    have hstep :
        (squareGridParameter N hN i.succ : ℝ) -
            (squareGridParameter N hN i.castSucc : ℝ) =
          1 / (N : ℝ) := by
      change
        ((i.succ : Fin (N + 1)) : ℝ) / N -
            ((i.castSucc : Fin (N + 1)) : ℝ) / N =
          1 / (N : ℝ)
      rw [
        show ((i.succ : Fin (N + 1)) : ℝ) = (i : ℝ) + 1 by norm_num,
        show ((i.castSucc : Fin (N + 1)) : ℝ) = (i : ℝ) by rfl
      ]
      ring
    change
      |(squareGridParameter N hN i.castSucc : ℝ) - (z.1 : ℝ)| ≤
        1 / (N : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr hxi0)]
    linarith
  · rw [Subtype.dist_eq, Real.dist_eq]
    have hstep :
        (squareGridParameter N hN j.succ : ℝ) -
            (squareGridParameter N hN j.castSucc : ℝ) =
          1 / (N : ℝ) := by
      change
        ((j.succ : Fin (N + 1)) : ℝ) / N -
            ((j.castSucc : Fin (N + 1)) : ℝ) / N =
          1 / (N : ℝ)
      rw [
        show ((j.succ : Fin (N + 1)) : ℝ) = (j : ℝ) + 1 by norm_num,
        show ((j.castSucc : Fin (N + 1)) : ℝ) = (j : ℝ) by rfl
      ]
      ring
    change
      |(squareGridParameter N hN j.castSucc : ℝ) - (z.2 : ℝ)| ≤
        1 / (N : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr hyj0)]
    linarith

/--
At one common subdivision count, every actual grid cell has a represented
vertex label whose open vertex star contains the image of the entire cell
under the relative null-homotopy.
-/
theorem exists_finite_squareGrid_vertexStar_control_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop) :
    ∃ N : Nat, ∃ hN : 0 < N,
      ∀ i j : Fin N,
        ∃ v, v ∈ vertexSupport K ∧
          ∀ z ∈ squareGridCell N hN i j,
            (H.homotopy z).1 ∈
              triangulationTopologicalVertexStar K v := by
  obtain ⟨N, hN, hcommon⟩ :=
    H.exists_uniform_vertexSupport_coordinate_positive_scale_probe

  refine ⟨N, hN, ?_⟩
  intro i j

  let a : unitInterval × unitInterval :=
    squareGridCellSource N hN i j

  obtain ⟨v, hvSupport, hvquarter⟩ :=
    carrier_exists_vertexSupport_coordinate_ge_quarter
      (H.homotopy a)

  refine ⟨v, hvSupport, ?_⟩
  intro z hz

  have hd :
      dist a z ≤ 1 / (N : ℝ) := by
    exact squareGridCell_dist_source_le N hN i j hz

  have hvpos :
      0 < (H.homotopy z).1 v := by
    exact hcommon v hvSupport a z hd hvquarter

  exact
    triangulationTopologicalVertexStar_mem_of_mem_space_of_coordinate_pos
      K v (H.homotopy z).2 hvpos



/--
Every parameter in the unit interval lies in one consecutive interval of the
standard equally-spaced `N`-subdivision.
-/
theorem exists_squareGrid_interval_index_probe
    (N : Nat) (hN : 0 < N) (t : unitInterval) :
    ∃ i : Fin N,
      (squareGridParameter N hN i.castSucc : ℝ) ≤ (t : ℝ) ∧
      (t : ℝ) ≤ (squareGridParameter N hN i.succ : ℝ) := by
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hN

  by_cases ht : (t : ℝ) = 1
  · have hNm1lt : N - 1 < N := by
      omega
    refine ⟨⟨N - 1, hNm1lt⟩, ?_, ?_⟩
    · change
        ((N - 1 : Nat) : ℝ) / (N : ℝ) ≤ (t : ℝ)
      rw [ht, div_le_one hNreal]
      exact_mod_cast Nat.sub_le N 1
    · change
        (t : ℝ) ≤
          (((N - 1) + 1 : Nat) : ℝ) / (N : ℝ)
      rw [ht]
      have hsub : N - 1 + 1 = N := by
        omega
      rw [hsub]
      simp [hNreal.ne']

  · have htlt : (t : ℝ) < 1 :=
      lt_of_le_of_ne t.property.2 ht

    have hx0 :
        0 ≤ (N : ℝ) * (t : ℝ) :=
      mul_nonneg (le_of_lt hNreal) t.property.1

    have hxlt :
        (N : ℝ) * (t : ℝ) < (N : ℝ) := by
      simpa using mul_lt_mul_of_pos_left htlt hNreal

    let q : Nat := ⌊(N : ℝ) * (t : ℝ)⌋₊

    have hqN : q < N := by
      dsimp [q]
      exact (Nat.floor_lt hx0).2 hxlt

    have hfloor :
        (q : ℝ) ≤ (N : ℝ) * (t : ℝ) := by
      dsimp [q]
      exact Nat.floor_le hx0

    have hupper :
        (N : ℝ) * (t : ℝ) <
          ((q + 1 : Nat) : ℝ) := by
      dsimp [q]
      simpa [Nat.cast_add] using
        (Nat.lt_floor_add_one ((N : ℝ) * (t : ℝ)))

    refine ⟨⟨q, hqN⟩, ?_, ?_⟩

    · change
        (q : ℝ) / (N : ℝ) ≤ (t : ℝ)
      rw [div_le_iff₀ hNreal]
      simpa [mul_comm] using hfloor

    · change
        (t : ℝ) ≤ ((q + 1 : Nat) : ℝ) / (N : ℝ)
      rw [le_div_iff₀ hNreal]
      exact le_of_lt (by
        simpa [mul_comm] using hupper)



/--
Every point of the full null-homotopy parameter square belongs to one actual
closed cell of the standard finite `N × N` subdivision.
-/
theorem exists_squareGridCell_containing_probe
    (N : Nat) (hN : 0 < N)
    (z : unitInterval × unitInterval) :
    ∃ i j : Fin N,
      z ∈ squareGridCell N hN i j := by
  obtain ⟨i, hxi0, hxi1⟩ :=
    exists_squareGrid_interval_index_probe N hN z.1

  obtain ⟨j, hyj0, hyj1⟩ :=
    exists_squareGrid_interval_index_probe N hN z.2

  refine ⟨i, j, ?_⟩
  exact ⟨hxi0, hxi1, hyj0, hyj1⟩



/-- The first standard grid parameter is exactly `0`. -/
theorem squareGridParameter_zero_probe
    (N : Nat) (hN : 0 < N) :
    squareGridParameter N hN 0 = 0 := by
  apply Subtype.ext
  simp [squareGridParameter]

/-- The final standard grid parameter is exactly `1`. -/
theorem squareGridParameter_last_probe
    (N : Nat) (hN : 0 < N) :
    squareGridParameter N hN (Fin.last N) = 1 := by
  apply Subtype.ext
  simp [squareGridParameter, hN.ne']




/--
Every point of the bottom side of the parameter square belongs to a grid cell
whose vertical cell index is exactly `0`.
-/
theorem exists_squareGrid_bottom_cell_probe
    (N : Nat) (hN : 0 < N) (t : unitInterval) :
    ∃ i : Fin N,
      (t, (0 : unitInterval)) ∈
        squareGridCell N hN i ⟨0, hN⟩ := by
  obtain ⟨i, hti0, hti1⟩ :=
    exists_squareGrid_interval_index_probe N hN t

  refine ⟨i, ?_⟩
  simp only [squareGridCell]
  refine ⟨hti0, hti1, ?_, ?_⟩

  · simp [squareGridParameter]

  · exact
      (squareGridParameter N hN
        ((⟨0, hN⟩ : Fin N).succ)).property.1



/--
Every point of the top side of the parameter square belongs to a grid cell
whose vertical cell index is the final element of `Fin N`.
-/
theorem exists_squareGrid_top_cell_probe
    (N : Nat) (hN : 0 < N) (t : unitInterval) :
    ∃ i : Fin N,
      (t, (1 : unitInterval)) ∈
        squareGridCell N hN i ⟨N - 1, by omega⟩ := by
  obtain ⟨i, hti0, hti1⟩ :=
    exists_squareGrid_interval_index_probe N hN t

  refine ⟨i, ?_⟩
  simp only [squareGridCell]
  refine ⟨hti0, hti1, ?_, ?_⟩

  · exact
      (squareGridParameter N hN
        ((⟨N - 1, by omega⟩ : Fin N).castSucc)).property.2

  · have hlast :
        ((⟨N - 1, by omega⟩ : Fin N).succ) = Fin.last N := by
      apply Fin.ext
      simp
      omega

    rw [hlast, squareGridParameter_last_probe]



/--
Every point of the left side of the parameter square belongs to a grid cell
whose horizontal cell index is exactly `0`.
-/
theorem exists_squareGrid_left_cell_probe
    (N : Nat) (hN : 0 < N) (t : unitInterval) :
    ∃ j : Fin N,
      ((0 : unitInterval), t) ∈
        squareGridCell N hN ⟨0, hN⟩ j := by
  obtain ⟨j, htj0, htj1⟩ :=
    exists_squareGrid_interval_index_probe N hN t

  refine ⟨j, ?_⟩
  simp only [squareGridCell]
  refine ⟨?_, ?_, htj0, htj1⟩

  · simp [squareGridParameter]

  · exact
      (squareGridParameter N hN
        ((⟨0, hN⟩ : Fin N).succ)).property.1



/--
Every point of the right side of the parameter square belongs to a grid cell
whose horizontal cell index is the final element of `Fin N`.
-/
theorem exists_squareGrid_right_cell_probe
    (N : Nat) (hN : 0 < N) (t : unitInterval) :
    ∃ j : Fin N,
      ((1 : unitInterval), t) ∈
        squareGridCell N hN ⟨N - 1, by omega⟩ j := by
  obtain ⟨j, htj0, htj1⟩ :=
    exists_squareGrid_interval_index_probe N hN t

  refine ⟨j, ?_⟩
  simp only [squareGridCell]
  refine ⟨?_, ?_, htj0, htj1⟩

  · exact
      (squareGridParameter N hN
        ((⟨N - 1, by omega⟩ : Fin N).castSucc)).property.2

  · have hlast :
        ((⟨N - 1, by omega⟩ : Fin N).succ) = Fin.last N := by
      apply Fin.ext
      simp
      omega

    rw [hlast, squareGridParameter_last_probe]



/--
The geometrically left side of the finite square grid is exactly the genuine
loop boundary of the null-homotopy.
-/
theorem exists_squareGrid_loopBoundary_cell_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N) (t : unitInterval) :
    ∃ j : Fin N,
      ((0 : unitInterval), t) ∈
          squareGridCell N hN ⟨0, hN⟩ j ∧
        H.homotopy ((0 : unitInterval), t) = loop t := by
  obtain ⟨j, hcell⟩ :=
    exists_squareGrid_left_cell_probe N hN t

  refine ⟨j, hcell, ?_⟩
  exact H.loop_boundary t



/--
The geometrically right side of the finite square grid is exactly the constant
boundary of the null-homotopy.
-/
theorem exists_squareGrid_constantBoundary_cell_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N) (t : unitInterval) :
    ∃ j : Fin N,
      ((1 : unitInterval), t) ∈
          squareGridCell N hN ⟨N - 1, by omega⟩ j ∧
        H.homotopy ((1 : unitInterval), t) = x := by
  obtain ⟨j, hcell⟩ :=
    exists_squareGrid_right_cell_probe N hN t

  refine ⟨j, hcell, ?_⟩
  exact H.constant_boundary t



/--
The geometrically bottom side of the finite square grid is exactly the source
boundary of the null-homotopy and is constant at `x`.
-/
theorem exists_squareGrid_sourceBoundary_cell_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N) (t : unitInterval) :
    ∃ i : Fin N,
      (t, (0 : unitInterval)) ∈
          squareGridCell N hN i ⟨0, hN⟩ ∧
        H.homotopy (t, (0 : unitInterval)) = x := by
  obtain ⟨i, hcell⟩ :=
    exists_squareGrid_bottom_cell_probe N hN t

  refine ⟨i, hcell, ?_⟩
  exact H.source_boundary t



/--
The geometrically top side of the finite square grid is exactly the target
boundary of the null-homotopy and is constant at `x`.
-/
theorem exists_squareGrid_targetBoundary_cell_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (N : Nat) (hN : 0 < N) (t : unitInterval) :
    ∃ i : Fin N,
      (t, (1 : unitInterval)) ∈
          squareGridCell N hN i ⟨N - 1, by omega⟩ ∧
        H.homotopy (t, (1 : unitInterval)) = x := by
  obtain ⟨i, hcell⟩ :=
    exists_squareGrid_top_cell_probe N hN t

  refine ⟨i, hcell, ?_⟩
  exact H.target_boundary t



/--
If the already-valid grid count `N` is refined to `N * 2^m`, then every
nonzero recursive `Path.trans` breakpoint `1 / 2^k`, for `k ≤ m`, is exactly
a point of the refined equally-spaced grid.
-/
theorem orderedTransition_dyadic_breakpoint_on_refined_grid_probe
    (N m k : Nat)
    (hN : 0 < N)
    (hk : k ≤ m) :
    (((N * 2 ^ (m - k) : Nat) : ℝ) /
        ((N * 2 ^ m : Nat) : ℝ)) =
      1 / ((2 ^ k : Nat) : ℝ) := by
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

  have hm : m = (m - k) + k := by
    omega

  rw [hm, pow_add]

  have hNreal : (N : ℝ) ≠ 0 := by
    exact_mod_cast hN.ne'

  have hpowleft : (2 : ℝ) ^ (m - k) ≠ 0 := by
    positivity

  have hpowright : (2 : ℝ) ^ k ≠ 0 := by
    positivity

  field_simp [hNreal, hpowleft, hpowright]
  congr 1
  omega



/--
Refining an already-valid grid count `N` by the dyadic factor `2^m`
produces a positive grid count and a weakly smaller mesh size.
-/
theorem orderedTransition_refined_grid_scale_probe
    (N m : Nat) (hN : 0 < N) :
    0 < N * 2 ^ m ∧
      (1 : ℝ) / ((N * 2 ^ m : Nat) : ℝ) ≤
        1 / (N : ℝ) := by
  constructor

  · have hp : 0 < 2 ^ m := by
      positivity
    exact Nat.mul_pos hN hp

  · have hNr : 0 < (N : ℝ) := by
      exact_mod_cast hN

    have hp :
        (1 : ℝ) ≤ (2 : ℝ) ^ m := by
      induction m with
      | zero =>
          simp
      | succ m ih =>
          rw [pow_succ]
          have hnonneg : 0 ≤ (2 : ℝ) ^ m := by
            positivity
          nlinarith

    have hden :
        (N : ℝ) ≤ (N : ℝ) * (2 : ℝ) ^ m := by
      nlinarith [le_of_lt hNr]

    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (one_div_le_one_div_of_le hNr hden)



/--
For any requested dyadic refinement depth `m`, the common star-control grid
can be refined from `N` to `N * 2^m` without losing whole-cell vertex-star
control.
-/
theorem exists_finite_squareGrid_dyadic_refinement_vertexStar_control_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (m : Nat) :
    ∃ N : Nat, ∃ hN : 0 < N,
      ∃ hD : 0 < N * 2 ^ m,
        ∀ i j : Fin (N * 2 ^ m),
          ∃ v, v ∈ vertexSupport K ∧
            ∀ z ∈ squareGridCell (N * 2 ^ m) hD i j,
              (H.homotopy z).1 ∈
                triangulationTopologicalVertexStar K v := by
  obtain ⟨N, hN, hcommon⟩ :=
    H.exists_uniform_vertexSupport_coordinate_positive_scale_probe

  have hscale :=
    orderedTransition_refined_grid_scale_probe N m hN

  refine ⟨N, hN, hscale.1, ?_⟩
  intro i j

  let a : unitInterval × unitInterval :=
    squareGridCellSource (N * 2 ^ m) hscale.1 i j

  obtain ⟨v, hvSupport, hvquarter⟩ :=
    carrier_exists_vertexSupport_coordinate_ge_quarter
      (H.homotopy a)

  refine ⟨v, hvSupport, ?_⟩
  intro z hz

  have hdRefined :
      dist a z ≤ 1 / ((N * 2 ^ m : Nat) : ℝ) := by
    exact
      squareGridCell_dist_source_le
        (N * 2 ^ m) hscale.1 i j hz

  have hdCommon :
      dist a z ≤ 1 / (N : ℝ) := by
    exact hdRefined.trans hscale.2

  have hvpos :
      0 < (H.homotopy z).1 v := by
    exact hcommon v hvSupport a z hdCommon hvquarter

  exact
    triangulationTopologicalVertexStar_mem_of_mem_space_of_coordinate_pos
      K v (H.homotopy z).2 hvpos

end CarrierLoopNullHomotopyData

end Poincare
