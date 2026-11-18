import Poincare.GlobalMove32ReentryDyadicGridVertices

/-!
# Boundary-compatible square grid at an arbitrary edge-walk length

A null-homotopy grid can be refined by the number of primal edge segments,
rather than only by a power of two. All equal-duration vertex breakpoints
then coincide with literal standard grid lines.

This does not construct the finite boundary chain or prove its equality
with the edge loop. It discharges the common finite scale/alignment input.
-/

namespace Poincare
namespace CarrierLoopNullHomotopyData

/-- Refining a positive coordinate scale by any positive integer preserves
the inverse-distance estimate needed for whole-cell positivity. -/
theorem edgeCount_refined_grid_scale
    (N m : Nat) (hN : 0 < N) (hm : 0 < m) :
    0 < N * m ∧
      (1 : ℝ) / ((N * m : Nat) : ℝ) ≤
        1 / (N : ℝ) := by
  have hD : 0 < N * m := Nat.mul_pos hN hm
  refine ⟨hD, ?_⟩
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmreal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden : (N : ℝ) ≤ (N : ℝ) * (m : ℝ) := by
    nlinarith
  simpa only [Nat.cast_mul] using
    (one_div_le_one_div_of_le hNr hden)

/-- The kth of m equally parameterized primal edge endpoints appears
literally at grid index N*k in an (N*m)-grid. -/
theorem edgeCount_breakpoint_refined_grid_vertex
    (N m k : Nat) (hN : 0 < N) (hm : 0 < m) (hk : k ≤ m) :
    ∃ i : Fin (N * m + 1),
      (squareGridParameter (N * m) (Nat.mul_pos hN hm) i : ℝ) =
        (k : ℝ) / (m : ℝ) := by
  have hindex : N * k < N * m + 1 := by
    have hmul : N * k ≤ N * m := Nat.mul_le_mul_left N hk
    omega
  let i : Fin (N * m + 1) := ⟨N * k, hindex⟩
  refine ⟨i, ?_⟩
  change (((N * k : Nat) : ℝ) / ((N * m : Nat) : ℝ)) =
    (k : ℝ) / (m : ℝ)
  have hnzero : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hmzero : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  push_cast
  field_simp
  ring

/-- Whole-cell coordinate positivity on an edge-count-refined grid.
The grid length is a multiple of m, so it supports *all* equal-time
edge-loop breakpoints. -/
theorem exists_edgeCount_refined_positiveCoordinate_labelling
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (m : Nat) (hm : 0 < m) :
    ∃ N : Nat, ∃ hN : 0 < N,
      ∃ hD : 0 < N * m,
        ∃ label : Fin (N * m) → Fin (N * m) → Nat,
          (∀ i j : Fin (N * m), label i j ∈ vertexSupport K) ∧
          ∀ i j : Fin (N * m),
            ∀ z ∈ squareGridCell (N * m) hD i j,
              0 < (H.homotopy z).1 (label i j) := by
  obtain ⟨N, hN, hcommon⟩ :=
    H.exists_uniform_vertexSupport_coordinate_positive_scale_probe
  have hscale := edgeCount_refined_grid_scale N m hN hm

  have hcells :
      ∀ i j : Fin (N * m),
        ∃ v, v ∈ vertexSupport K ∧
          ∀ z ∈ squareGridCell (N * m) hscale.1 i j,
            0 < (H.homotopy z).1 v := by
    intro i j
    let a : unitInterval × unitInterval :=
      squareGridCellSource (N * m) hscale.1 i j
    obtain ⟨v, hvSupport, hvquarter⟩ :=
      carrier_exists_vertexSupport_coordinate_ge_quarter (H.homotopy a)
    refine ⟨v, hvSupport, ?_⟩
    intro z hz
    have hdRefined :
        dist a z ≤ 1 / ((N * m : Nat) : ℝ) :=
      squareGridCell_dist_source_le (N * m) hscale.1 i j hz
    have hdCommon : dist a z ≤ 1 / (N : ℝ) :=
      hdRefined.trans hscale.2
    exact hcommon v hvSupport a z hdCommon hvquarter
  choose label hlabel using hcells
  refine ⟨N, hN, hscale.1, label, ?_, ?_⟩
  · intro i j
    exact (hlabel i j).1
  · intro i j z hz
    exact (hlabel i j).2 z hz

#print axioms edgeCount_refined_grid_scale
#print axioms edgeCount_breakpoint_refined_grid_vertex
#print axioms exists_edgeCount_refined_positiveCoordinate_labelling

end CarrierLoopNullHomotopyData
end Poincare
