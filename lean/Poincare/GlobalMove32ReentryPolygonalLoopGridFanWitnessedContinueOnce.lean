import Poincare.GlobalMove32ReentryPolygonalLoopGridFanWitnessedStep

namespace Poincare

/-- Consume exactly one recursive `FanChordTransition` output of the witnessed
square-grid fan/chord step using `FanChordTransition.continue_witnessed`.
The four certified exits are retained, while the remaining recursive branch
records the transition that was consumed together with its next transition.
No termination or normalization claim is made. -/
theorem ClosedTriangulationCore.distinct_positive_grid_cell_labels_witnessed_fanChord_continue_once
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
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
    (∃ p q sigma,
      p ≠ q ∧
      sigma ∈ K.tets ∧
      p ∈ sigma.verts ∧
      q ∈ sigma.verts ∧
      4 ≤
        (K.tets.filter
          (fun gamma =>
            decide (p ∈ gamma.verts ∧ q ∈ gamma.verts))).length) ∨
    (∃ s s' : Move32Site,
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      Move32SourceFaceWitnessedReentry K s s') ∨
    (∃ T : FanChordTransition K v x,
      Nonempty (FanChordTransition K T.z0 T.z1)) := by
  rcases
      hcore.distinct_positive_grid_cell_labels_witnessed_fanChord_step
        hM hlinks hconn hNoFour H hvx hv hx hzLeft hzRight with
    hmove23 | hdescent | hhigh | hreentry | htransition
  · exact Or.inl hmove23
  · exact Or.inr (Or.inl hdescent)
  · rcases hhigh with
      ⟨_s, p, q, sigma,
        _hsd, _hse, _hrealized, _hthree,
        hpq, hsigma, hp, hq, _hnonself, hinc⟩
    exact Or.inr (Or.inr (Or.inl ⟨p, q, sigma, hpq, hsigma, hp, hq, hinc⟩))
  · rcases hreentry with
      ⟨s, s', _hsd, _hse, hrealized, hthree, hwitnessed⟩
    exact
      Or.inr
        (Or.inr
          (Or.inr
            (Or.inl ⟨s, s', hrealized, hthree, hwitnessed⟩)))
  · obtain ⟨T⟩ := htransition
    rcases
        ClosedTriangulationCore.FanChordTransition.continue_witnessed
          hcore hM hlinks hconn hNoFour T with
      hmove23 | hdescent | hhigh | hreentry | hnext
    · exact Or.inl hmove23
    · exact Or.inr (Or.inl hdescent)
    · exact Or.inr (Or.inr (Or.inl hhigh))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hreentry)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨T, hnext⟩)))

end Poincare
