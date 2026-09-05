import Poincare.GlobalHighEdgeToFanState
import Poincare.GlobalFanChordTransition

namespace Poincare

/-- Continue a fan-chord transition without assuming that source-obstruction
high edges are absent.  Any such high edge is immediately rebuilt as its own
high-fan state.  The only remaining one-step exits are a legal `2-3` move,
strict topology-preserving `PhiSupport` descent, witnessed source-face reentry,
or another high-fan state. -/
theorem ClosedTriangulationCore.FanChordTransition.continue_reinjectHigh
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
    {v x : Nat}
    (T : FanChordTransition K v x) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∃ s s' : Move32Site,
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      Move32SourceFaceWitnessedReentry K s s') ∨
    Nonempty (HighFanState K) := by
  rcases
      ClosedTriangulationCore.FanChordTransition.continue_witnessed
        hcore hM hlinks hconn hNoFour T with
    hmove23 | hdescent | hhigh | hreentry | hnext

  · exact Or.inl hmove23

  · exact Or.inr (Or.inl hdescent)

  · obtain ⟨p, q, sigma, hpq, hsigma, hp, hq, hinc⟩ := hhigh
    have hinc' :
        4 ≤ (K.tets.filter
          (fun gamma => p ∈ gamma.verts ∧ q ∈ gamma.verts)).length := by
      simpa using hinc

    rcases
        hcore.exists_legal_move23_or_highFanState_of_edgeIncidence_four_le
          hM hpq hsigma hp hq hinc' with
      hmove23 | hstate

    · exact Or.inl hmove23
    · exact Or.inr (Or.inr (Or.inr hstate))

  · exact Or.inr (Or.inr (Or.inl hreentry))

  · obtain ⟨T'⟩ := hnext
    exact
      Or.inr
        (Or.inr
          (Or.inr
            ⟨{
              v := T.z0
              x := T.z1
              v_supported := T.z0_supported
              x_supported := T.z1_supported
              endpoints_ne := T.endpoints_ne
              transition := T'
            }⟩))

end Poincare
