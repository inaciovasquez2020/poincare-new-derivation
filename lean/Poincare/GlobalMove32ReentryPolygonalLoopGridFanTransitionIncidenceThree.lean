import Poincare.GlobalMove32ReentryPolygonalLoopGridFanTransition

namespace Poincare

/-- Consume only the incidence-three output of the grid-induced fan/chord
transition.  The legal `2-3` branch and the recursive chord-transition branch
are retained unchanged. -/
theorem ClosedTriangulationCore.distinct_positive_grid_cell_labels_fanChordTransition_or_descent_or_sourceFace
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
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
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∃ s : Move32Site,
      s.d = v ∧
      s.e = x ∧
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts) ∨
    Nonempty (FanChordTransition K v x) := by
  rcases
      hcore.distinct_positive_grid_cell_labels_fanChordTransition
        hM H hvx hv hx hzLeft hzRight with
    hmove23 | hthree | htransition
  · exact Or.inl hmove23
  · rcases
      hcore.exists_descent_or_realized_sourceFace_obstruction_of_edgeIncidence_three
        hNoFour v x hvx (by simpa using hthree) with
      hdescent | hobstruction
    · exact Or.inr (Or.inl hdescent)
    · exact Or.inr (Or.inr (Or.inl hobstruction))
  · exact Or.inr (Or.inr (Or.inr htransition))

end Poincare
