import Poincare.GlobalMove32ReentryPolygonalLoopGridFanTransitionIncidenceThree
import Poincare.GlobalMove32WitnessedSourceFaceReentry

namespace Poincare

/-- Consume only the concrete source-face-obstruction output of the grid-induced
fan transition through the witnessed source-face classifier.  The legal
`2-3`, strict-descent, high complementary-edge, witnessed-reentry, and
recursive chord-transition alternatives are all retained; no termination
claim is made here. -/
theorem ClosedTriangulationCore.distinct_positive_grid_cell_labels_witnessed_fanChord_step
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
    (∃ s : Move32Site,
      ∃ p q sigma,
        s.d = v ∧
        s.e = x ∧
        s.RealizedIn K ∧
        s.SharedEdgeExactlyThree K ∧
        p ≠ q ∧
        sigma ∈ K.tets ∧
        p ∈ sigma.verts ∧
        q ∈ sigma.verts ∧
        ¬ ((p = s.d ∧ q = s.e) ∨ (p = s.e ∧ q = s.d)) ∧
        4 ≤
          (K.tets.filter
            (fun gamma =>
              decide (p ∈ gamma.verts ∧ q ∈ gamma.verts))).length) ∨
    (∃ s s' : Move32Site,
      s.d = v ∧
      s.e = x ∧
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      Move32SourceFaceWitnessedReentry K s s') ∨
    Nonempty (FanChordTransition K v x) := by
  rcases
      hcore.distinct_positive_grid_cell_labels_fanChordTransition_or_descent_or_sourceFace
        hM hNoFour H hvx hv hx hzLeft hzRight with
    hmove23 | hdescent | hobstruction | htransition
  · exact Or.inl hmove23
  · exact Or.inr (Or.inl hdescent)
  · rcases hobstruction with
      ⟨s, hsd, hse, hrealized, hthree, hsource⟩
    rcases
        hcore.exists_legal_move23_or_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
          hlinks hconn hNoFour s hrealized hsource with
      hmove23 | hdescent | hhigh | hreentry
    · rcases hmove23 with ⟨m, _ha, _hb, _hc, hlegal⟩
      exact Or.inl ⟨m, hlegal⟩
    · exact Or.inr (Or.inl hdescent)
    · rcases hhigh with
        ⟨p, q, sigma, hpq, hsigma, hp, hq, hnonself, hinc⟩
      exact
        Or.inr
          (Or.inr
            (Or.inl
              ⟨s, p, q, sigma,
                hsd, hse, hrealized, hthree,
                hpq, hsigma, hp, hq, hnonself, hinc⟩))
    · rcases hreentry with ⟨s', hwitnessed⟩
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inl
                ⟨s, s', hsd, hse, hrealized, hthree, hwitnessed⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr htransition)))

end Poincare
