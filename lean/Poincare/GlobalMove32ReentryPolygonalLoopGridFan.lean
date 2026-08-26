import Poincare.GlobalMove32ReentryPolygonalLoopGridEdge
import Poincare.GlobalEdgeCyclicFan

namespace Poincare

/-- Distinct positive labels on two meeting null-homotopy grid cells determine
an actual represented edge, and the honest manifold structure upgrades that
edge to the ambient cyclic fan consumed by the fan/chord transition API. -/
theorem ClosedTriangulationCore.exists_ambientEdgeCyclicFan_of_distinct_positive_grid_cell_labels
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
    Nonempty (AmbientEdgeCyclicFan K v x) := by
  rcases
      CarrierLoopNullHomotopyData.squareGridCell_positive_labels_eq_or_vertexLinkVertexRepresented
        H hv hx hzLeft hzRight with
    heq | hrep
  · exact (hvx heq).elim
  · exact hcore.exists_ambientEdgeCyclicFan_of_topologicalThreeManifold hM hrep

end Poincare
