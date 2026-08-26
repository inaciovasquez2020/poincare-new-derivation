import Poincare.GlobalMove32ReentryPolygonalLoopGridFan
import Poincare.GlobalFanChordTransition

namespace Poincare

/-- Distinct positive labels on two meeting null-homotopy grid cells enter the
existing ambient-fan chord transition.  No branch is eliminated here: the
output is exactly the local transition API already proved for an adjacent fan
pair. -/
theorem ClosedTriangulationCore.distinct_positive_grid_cell_labels_fanChordTransition
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {x0 : triangulationTopologicalGeometricCarrier K}
    {loop : Path x0 x0}
    (H : CarrierLoopNullHomotopyData K x0 loop)
    {D : Nat} {hD : 0 < D}
    {i j i' j' : Fin D}
    {v x : Nat}
    (hvx : v ≠ x)
    (hv :
      ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i j,
        0 < (H.homotopy z).1 v)
    (hx :
      ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i' j',
        0 < (H.homotopy z).1 x)
    {z : unitInterval × unitInterval}
    (hzLeft :
      z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i j)
    (hzRight :
      z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i' j') :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (K.tets.filter (fun t => v ∈ t.verts ∧ x ∈ t.verts)).length = 3 ∨
    Nonempty (FanChordTransition K v x) := by
  obtain ⟨F⟩ :=
    hcore.exists_ambientEdgeCyclicFan_of_distinct_positive_grid_cell_labels
      hM H hvx hv hx hzLeft hzRight
  obtain ⟨sigma, rho, hadj⟩ := F.exists_adjacent
  exact hcore.ambientEdgeCyclicFan_adjacent_transition hM F hadj

end Poincare
