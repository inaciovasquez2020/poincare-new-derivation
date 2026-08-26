import Poincare.GlobalMove32ReentryPolygonalLoopNullHomotopy

namespace Poincare

namespace CarrierLoopNullHomotopyData

/--
The dyadically refined null-homotopy grid can retain the strict-positive
coordinate statement used internally to obtain vertex-star control.

This is the first cell-to-edge bridge input: if two neighboring cells are
labelled by vertices whose coordinates stay positive on the whole cells,
then at any shared boundary point both coordinates are positive.  A later
bridge can therefore recover an actual represented tetrahedron containing
both labels, rather than only two possibly degenerate vertex-star memberships.
-/
theorem exists_finite_squareGrid_dyadic_refinement_positiveCoordinate_control
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
              0 < (H.homotopy z).1 v := by
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

  exact hcommon v hvSupport a z hdCommon hvquarter

end CarrierLoopNullHomotopyData

end Poincare
