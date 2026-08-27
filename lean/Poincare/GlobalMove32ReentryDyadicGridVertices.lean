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

end CarrierLoopNullHomotopyData
end Poincare
