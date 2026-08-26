import Poincare.GlobalMove32ReentryPolygonalLoopPositiveGrid
import Poincare.CarrierPositiveCoordinateRepresentedEdge

namespace Poincare

namespace CarrierLoopNullHomotopyData

/-- Labels controlling two grid cells that meet at a common parameter point
are either the same label or form a represented edge.  The distinct-label
branch is the exact input consumed by the ambient cyclic-fan API. -/
theorem squareGridCell_positive_labels_eq_or_vertexLinkVertexRepresented
    {K : Triangulation}
    {x0 : triangulationTopologicalGeometricCarrier K}
    {loop : Path x0 x0}
    (H : CarrierLoopNullHomotopyData K x0 loop)
    {D : Nat} {hD : 0 < D}
    {i j i' j' : Fin D}
    {v x : Nat}
    (hv :
      ∀ z ∈ squareGridCell D hD i j,
        0 < (H.homotopy z).1 v)
    (hx :
      ∀ z ∈ squareGridCell D hD i' j',
        0 < (H.homotopy z).1 x)
    {z : unitInterval × unitInterval}
    (hzLeft : z ∈ squareGridCell D hD i j)
    (hzRight : z ∈ squareGridCell D hD i' j') :
    v = x ∨ VertexLinkVertexRepresented K v x := by
  by_cases hvx : v = x
  · exact Or.inl hvx
  · exact Or.inr
      (vertexLinkVertexRepresented_of_positive_coordinates
        (H.homotopy z) hvx
        (hv z hzLeft) (hx z hzRight))

end CarrierLoopNullHomotopyData

end Poincare
