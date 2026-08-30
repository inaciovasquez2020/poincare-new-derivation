import Poincare.GlobalMove32ReentryPolygonalLoopNullHomotopy

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
Every nonzero recursive `Path.trans` dyadic breakpoint is literally a vertex
of the refined equally-spaced grid.  The grid index is the exact integer
`N * 2^(m-k)` inside `Fin (N * 2^m + 1)`.
-/
theorem orderedTransition_dyadic_breakpoint_refined_grid_vertex_probe
    (N m k : Nat)
    (hN : 0 < N)
    (hk : k ≤ m) :
    ∃ i : Fin (N * 2 ^ m + 1),
      (squareGridParameter
          (N * 2 ^ m)
          (orderedTransition_refined_grid_scale_probe N m hN).1
          i : ℝ) =
        1 / ((2 ^ k : Nat) : ℝ) := by
  have hpow :
      2 ^ (m - k) ≤ 2 ^ m := by
    exact
      Nat.pow_le_pow_right
        (by omega)
        (Nat.sub_le m k)

  have hindex :
      N * 2 ^ (m - k) < N * 2 ^ m + 1 := by
    have hmul :
        N * 2 ^ (m - k) ≤ N * 2 ^ m :=
      Nat.mul_le_mul_left N hpow
    omega

  let i : Fin (N * 2 ^ m + 1) :=
    ⟨N * 2 ^ (m - k), hindex⟩

  refine ⟨i, ?_⟩

  change
    (((N * 2 ^ (m - k) : Nat) : ℝ) /
        ((N * 2 ^ m : Nat) : ℝ)) =
      1 / ((2 ^ k : Nat) : ℝ)

  exact
    orderedTransition_dyadic_breakpoint_on_refined_grid_probe
      N m k hN hk

/--
At one common finite square-grid scale, every cell has a represented vertex
whose carrier coordinate stays strictly positive on the entire cell.  This
retains the open-star witness used internally by the existing cell-control
proof instead of weakening it to closed vertex-star membership.
-/
theorem exists_finite_squareGrid_positiveCoordinate_control_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop) :
    ∃ N : Nat, ∃ hN : 0 < N,
      ∀ i j : Fin N,
        ∃ v, v ∈ vertexSupport K ∧
          ∀ z ∈ squareGridCell N hN i j,
            0 < (H.homotopy z).1 v := by
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

  exact hcommon v hvSupport a z hd hvquarter

/--
Package the cellwise positive-coordinate witnesses into one finite label map.
This is the first explicit finite combinatorial object extracted from the
relative null-homotopy.
-/
theorem exists_finite_squareGrid_positiveCoordinate_labelling_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop) :
    ∃ N : Nat, ∃ hN : 0 < N,
      ∃ label : Fin N → Fin N → Nat,
        (∀ i j : Fin N,
          label i j ∈ vertexSupport K) ∧
        ∀ i j : Fin N,
          ∀ z ∈ squareGridCell N hN i j,
            0 < (H.homotopy z).1 (label i j) := by
  obtain ⟨N, hN, hcells⟩ :=
    H.exists_finite_squareGrid_positiveCoordinate_control_probe

  choose label hlabel using hcells

  refine ⟨N, hN, label, ?_, ?_⟩
  · intro i j
    exact (hlabel i j).1
  · intro i j z hz
    exact (hlabel i j).2 z hz

/--
Two strictly positive carrier coordinates at one point are represented in a
common tetrahedron.  This is the local compatibility mechanism for labels of
neighboring filling cells.
-/
theorem carrier_two_positive_coordinates_common_tet_probe
    {K : Triangulation}
    (p : triangulationTopologicalGeometricCarrier K)
    {v w : Nat}
    (hv : 0 < p.1 v)
    (hw : 0 < p.1 w) :
    ∃ tau : Tet,
      tau ∈ K.tets ∧
      v ∈ tau.verts ∧
      w ∈ tau.verts := by
  obtain ⟨F, _, tau, htau, hFtau, a, _, _, hap⟩ :=
    carrier_exists_finite_barycentric_support p

  have hvF : v ∈ F := by
    by_contra hvF
    have hz : p.1 v = 0 := by
      rw [geometricVertex_weighted_sum_coordinate F a p.1 hap v]
      simp [hvF]
    linarith

  have hwF : w ∈ F := by
    by_contra hwF
    have hz : p.1 w = 0 := by
      rw [geometricVertex_weighted_sum_coordinate F a p.1 hap w]
      simp [hwF]
    linarith

  exact ⟨
    tau,
    htau,
    List.mem_toFinset.mp (hFtau hvF),
    List.mem_toFinset.mp (hFtau hwF)
  ⟩

/--
The finite positive-coordinate filling can be labelled so that any two cells
which meet have labels occurring together in one represented tetrahedron.
This packages the local compatibility fact in exactly the form needed before
proving the horizontal and vertical shared-grid-point cases.
-/
theorem exists_finite_squareGrid_overlap_compatible_labelling_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop) :
    ∃ N : Nat, ∃ hN : 0 < N,
      ∃ label : Fin N → Fin N → Nat,
        (∀ i j : Fin N,
          label i j ∈ vertexSupport K) ∧
        (∀ i j : Fin N,
          ∀ z ∈ squareGridCell N hN i j,
            0 < (H.homotopy z).1 (label i j)) ∧
        ∀ i j i' j' : Fin N,
          ∀ z,
            z ∈ squareGridCell N hN i j →
            z ∈ squareGridCell N hN i' j' →
            ∃ tau : Tet,
              tau ∈ K.tets ∧
              label i j ∈ tau.verts ∧
              label i' j' ∈ tau.verts := by
  obtain ⟨N, hN, label, hsupport, hpositive⟩ :=
    H.exists_finite_squareGrid_positiveCoordinate_labelling_probe

  refine ⟨N, hN, label, hsupport, hpositive, ?_⟩
  intro i j i' j' z hz hz'

  exact carrier_two_positive_coordinates_common_tet_probe
    (H.homotopy z)
    (hpositive i j z hz)
    (hpositive i' j' z hz')

/-- The southwest corner of every standard cell belongs to that closed cell. -/
theorem squareGridCellSource_mem_probe
    (N : Nat) (hN : 0 < N) (i j : Fin N) :
    squareGridCellSource N hN i j ∈ squareGridCell N hN i j := by
  have hNr : 0 < (N : ℝ) := by
    exact_mod_cast hN

  simp only [squareGridCell, squareGridCellSource]
  refine ⟨le_rfl, ?_, le_rfl, ?_⟩

  · change
      ((i : ℝ) / (N : ℝ)) ≤
        (((i.succ : Fin (N + 1)) : ℝ) / (N : ℝ))
    rw [show ((i.succ : Fin (N + 1)) : ℝ) = (i : ℝ) + 1 by norm_num,
      div_le_div_iff₀ hNr hNr]
    nlinarith

  · change
      ((j : ℝ) / (N : ℝ)) ≤
        (((j.succ : Fin (N + 1)) : ℝ) / (N : ℝ))
    rw [show ((j.succ : Fin (N + 1)) : ℝ) = (j : ℝ) + 1 by norm_num,
      div_le_div_iff₀ hNr hNr]
    nlinarith

/-- Consecutive horizontal or vertical grid cells meet in an explicit corner. -/
theorem squareGridCell_neighbor_overlap_probe
    (N : Nat) (hN : 0 < N) :
    (∀ i i' j : Fin N,
      (i : Nat) + 1 = (i' : Nat) →
      ∃ z,
        z ∈ squareGridCell N hN i j ∧
        z ∈ squareGridCell N hN i' j) ∧
    (∀ i j j' : Fin N,
      (j : Nat) + 1 = (j' : Nat) →
      ∃ z,
        z ∈ squareGridCell N hN i j ∧
        z ∈ squareGridCell N hN i j') := by
  constructor
  · intro i i' j hii
    let z := squareGridCellSource N hN i' j
    refine ⟨z, ?_, squareGridCellSource_mem_probe N hN i' j⟩

    have hleft := squareGridCellSource_mem_probe N hN i j
    have hi : i'.castSucc = i.succ := by
      apply Fin.ext
      exact hii.symm

    dsimp [z]
    simp only [squareGridCell, squareGridCellSource] at hleft ⊢
    rcases hleft with ⟨_, hxup, _, hyup⟩
    rw [hi]
    exact ⟨hxup, le_rfl, le_rfl, hyup⟩

  · intro i j j' hjj
    let z := squareGridCellSource N hN i j'
    refine ⟨z, ?_, squareGridCellSource_mem_probe N hN i j'⟩

    have hbelow := squareGridCellSource_mem_probe N hN i j
    have hj : j'.castSucc = j.succ := by
      apply Fin.ext
      exact hjj.symm

    dsimp [z]
    simp only [squareGridCell, squareGridCellSource] at hbelow ⊢
    rcases hbelow with ⟨_, hxup, _, hyup⟩
    rw [hj]
    exact ⟨le_rfl, hxup, hyup, le_rfl⟩

/--
The finite filling labels are compatible across every horizontal and vertical
grid edge: consecutive cell labels occur together in one represented
tetrahedron.
-/
theorem exists_finite_squareGrid_neighbor_tet_compatible_labelling_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop) :
    ∃ N : Nat, ∃ hN : 0 < N,
      ∃ label : Fin N → Fin N → Nat,
        (∀ i j : Fin N,
          label i j ∈ vertexSupport K) ∧
        (∀ i j : Fin N,
          ∀ z ∈ squareGridCell N hN i j,
            0 < (H.homotopy z).1 (label i j)) ∧
        (∀ i i' j : Fin N,
          (i : Nat) + 1 = (i' : Nat) →
          ∃ tau : Tet,
            tau ∈ K.tets ∧
            label i j ∈ tau.verts ∧
            label i' j ∈ tau.verts) ∧
        ∀ i j j' : Fin N,
          (j : Nat) + 1 = (j' : Nat) →
          ∃ tau : Tet,
            tau ∈ K.tets ∧
            label i j ∈ tau.verts ∧
            label i j' ∈ tau.verts := by
  obtain ⟨N, hN, label, hsupport, hpositive, hoverlap⟩ :=
    H.exists_finite_squareGrid_overlap_compatible_labelling_probe
  obtain ⟨hhorizontal, hvertical⟩ :=
    squareGridCell_neighbor_overlap_probe N hN

  refine ⟨N, hN, label, hsupport, hpositive, ?_, ?_⟩

  · intro i i' j hii
    obtain ⟨z, hz, hz'⟩ := hhorizontal i i' j hii
    exact hoverlap i j i' j z hz hz'

  · intro i j j' hjj
    obtain ⟨z, hz, hz'⟩ := hvertical i j j' hjj
    exact hoverlap i j i j' z hz hz'

/--
At any requested dyadic refinement depth, retain strict positive-coordinate
cell labels on the refined grid `D = N * 2^m`.  This is the refined analogue
of the finite labelling above and is the scale needed to place every recursive
`Path.trans` breakpoint literally on the left boundary grid.
-/
theorem exists_finite_squareGrid_dyadic_refinement_positiveCoordinate_labelling_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (m : Nat) :
    ∃ N : Nat, ∃ hN : 0 < N,
      ∃ hD : 0 < N * 2 ^ m,
        ∃ label : Fin (N * 2 ^ m) → Fin (N * 2 ^ m) → Nat,
          (∀ i j : Fin (N * 2 ^ m),
            label i j ∈ vertexSupport K) ∧
          ∀ i j : Fin (N * 2 ^ m),
            ∀ z ∈ squareGridCell (N * 2 ^ m) hD i j,
              0 < (H.homotopy z).1 (label i j) := by
  obtain ⟨N, hN, hcommon⟩ :=
    H.exists_uniform_vertexSupport_coordinate_positive_scale_probe

  have hscale :=
    orderedTransition_refined_grid_scale_probe N m hN

  have hcells :
      ∀ i j : Fin (N * 2 ^ m),
        ∃ v, v ∈ vertexSupport K ∧
          ∀ z ∈ squareGridCell (N * 2 ^ m) hscale.1 i j,
            0 < (H.homotopy z).1 v := by
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

    exact hcommon v hvSupport a z hdCommon hvquarter

  choose label hlabel using hcells

  refine ⟨N, hN, hscale.1, label, ?_, ?_⟩
  · intro i j
    exact (hlabel i j).1
  · intro i j z hz
    exact (hlabel i j).2 z hz

/--
At the same requested dyadic refinement depth, consecutive refined-cell
labels across every horizontal and vertical grid edge occur together in one
represented tetrahedron.
-/
theorem exists_finite_squareGrid_dyadic_refinement_neighbor_tet_compatible_labelling_probe
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (m : Nat) :
    ∃ N : Nat, ∃ hN : 0 < N,
      ∃ hD : 0 < N * 2 ^ m,
        ∃ label : Fin (N * 2 ^ m) → Fin (N * 2 ^ m) → Nat,
          (∀ i j : Fin (N * 2 ^ m),
            label i j ∈ vertexSupport K) ∧
          (∀ i j : Fin (N * 2 ^ m),
            ∀ z ∈ squareGridCell (N * 2 ^ m) hD i j,
              0 < (H.homotopy z).1 (label i j)) ∧
          (∀ i i' j : Fin (N * 2 ^ m),
            (i : Nat) + 1 = (i' : Nat) →
            ∃ tau : Tet,
              tau ∈ K.tets ∧
              label i j ∈ tau.verts ∧
              label i' j ∈ tau.verts) ∧
          ∀ i j j' : Fin (N * 2 ^ m),
            (j : Nat) + 1 = (j' : Nat) →
            ∃ tau : Tet,
              tau ∈ K.tets ∧
              label i j ∈ tau.verts ∧
              label i j' ∈ tau.verts := by
  obtain ⟨N, hN, hD, label, hsupport, hpositive⟩ :=
    H.exists_finite_squareGrid_dyadic_refinement_positiveCoordinate_labelling_probe m

  obtain ⟨hhorizontal, hvertical⟩ :=
    squareGridCell_neighbor_overlap_probe (N * 2 ^ m) hD

  refine ⟨N, hN, hD, label, hsupport, hpositive, ?_, ?_⟩

  · intro i i' j hii
    obtain ⟨z, hz, hz'⟩ := hhorizontal i i' j hii
    exact carrier_two_positive_coordinates_common_tet_probe
      (H.homotopy z)
      (hpositive i j z hz)
      (hpositive i' j z hz')

  · intro i j j' hjj
    obtain ⟨z, hz, hz'⟩ := hvertical i j j' hjj
    exact carrier_two_positive_coordinates_common_tet_probe
      (H.homotopy z)
      (hpositive i j z hz)
      (hpositive i j' z hz')

end CarrierLoopNullHomotopyData
end Poincare
