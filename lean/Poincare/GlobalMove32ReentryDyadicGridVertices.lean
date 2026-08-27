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

end CarrierLoopNullHomotopyData
end Poincare
