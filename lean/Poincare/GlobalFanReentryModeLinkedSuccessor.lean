import Poincare.GlobalFanReentryModeLinkedStep
import Poincare.GlobalHighEdgeToFanStateWithEndpoints
import Poincare.GlobalDegreeFourDescent
import Poincare.TriangulationTopologicalManifoldConnectedLinkClosedCore
import Poincare.TriangulationTopologicalHonestConnectedness

namespace Poincare

/-- Under the fail-closed assumptions excluding legal `2-3` moves and strict
`PhiSupport` descent, every mixed fan/reentry obstruction has a lineage-
preserving successor.  Honest manifoldness supplies the combinatorial
connectivity hypotheses, while positive support plus no descent forces the
no-degree-four branch. -/
theorem ClosedTriangulationCore.exists_fanReentryModeStep_of_noMove23_noDescent
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hphi : 0 < PhiSupport K)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (q : FanReentryModeState K) :
    ∃ q' : FanReentryModeState K,
      FanReentryModeStep K q q' := by
  have hconnected : ConnectedLinkClosedCore K :=
    connectedLinkClosedCore_of_topologicalThreeManifold K hcore hM
  have hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v :=
    hconnected.2
  have hconn : TetrahedronVertexOverlapConnected K :=
    hcore.tetrahedronVertexOverlapConnected_of_topologicalThreeManifold hM
  have hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4 := by
    rcases
        hcore.exists_topology_preserving_PhiSupport_descent_or_no_degree_four
          hlinks hconn hphi with
      hdescent | hNoFour
    · exact (hNoDescent hdescent).elim
    · exact hNoFour

  cases q with
  | fan old =>
      rcases
          ClosedTriangulationCore.FanChordTransition.continue
            hcore hM hNoFour old.transition with
        hmove23 | hdescent | hobstruction | hnext

      · exact (hNoMove23 hmove23).elim
      · exact (hNoDescent hdescent).elim
      · obtain ⟨s, hsd, hse, hrealized, hthree, hsource⟩ := hobstruction
        rcases
            hcore.exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
              hlinks hconn hNoFour s hrealized hsource with
          hdescent | hhigh | hreentry
        · exact (hNoDescent hdescent).elim
        · obtain ⟨p, r, sigma, hpr, hsigma, hp, hr, hnonself, hinc⟩ := hhigh
          have hinc' :
              4 ≤ (K.tets.filter
                (fun gamma => p ∈ gamma.verts ∧ r ∈ gamma.verts)).length := by
            simpa using hinc
          rcases
              hcore.exists_legal_move23_or_highFanState_on_edge_of_edgeIncidence_four_le
                hM hpr hsigma hp hr hinc' with
            hmove23 | hstate
          · exact (hNoMove23 hmove23).elim
          · obtain ⟨next, hv, hx⟩ := hstate
            have hnonself' :
                ¬ ((next.v = s.d ∧ next.x = s.e) ∨
                   (next.v = s.e ∧ next.x = s.d)) := by
              intro hself
              rw [hv, hx] at hself
              exact hnonself hself
            exact
              ⟨FanReentryModeState.fan next,
                FanReentryModeStep.fan_reinject
                  old next s hsd hse hrealized hsource hnonself'⟩
        · obtain ⟨s', hstep⟩ := hreentry
          exact
            ⟨FanReentryModeState.reentry
                (witnessedReentryStateOfStep hstep),
              FanReentryModeStep.fan_reentry
                old s s' hsd hse hrealized hthree hstep⟩
      · obtain ⟨T'⟩ := hnext
        let next : HighFanState K :=
          {
            v := old.transition.z0
            x := old.transition.z1
            v_supported := old.transition.z0_supported
            x_supported := old.transition.z1_supported
            endpoints_ne := old.transition.endpoints_ne
            transition := T'
          }
        exact
          ⟨FanReentryModeState.fan next,
            FanReentryModeStep.fan_next old next rfl rfl⟩

  | reentry old =>
      rcases
          hcore.exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
            hlinks hconn hNoFour old.site old.realized old.obstruction with
        hdescent | hhigh | hreentry

      · exact (hNoDescent hdescent).elim
      · obtain ⟨p, r, sigma, hpr, hsigma, hp, hr, hnonself, hinc⟩ := hhigh
        have hinc' :
            4 ≤ (K.tets.filter
              (fun gamma => p ∈ gamma.verts ∧ r ∈ gamma.verts)).length := by
          simpa using hinc
        rcases
            hcore.exists_legal_move23_or_highFanState_on_edge_of_edgeIncidence_four_le
              hM hpr hsigma hp hr hinc' with
          hmove23 | hstate
        · exact (hNoMove23 hmove23).elim
        · obtain ⟨next, hv, hx⟩ := hstate
          have hnonself' :
              ¬ ((next.v = old.site.d ∧ next.x = old.site.e) ∨
                 (next.v = old.site.e ∧ next.x = old.site.d)) := by
            intro hself
            rw [hv, hx] at hself
            exact hnonself hself
          exact
            ⟨FanReentryModeState.fan next,
              FanReentryModeStep.reentry_fan old next hnonself'⟩
      · obtain ⟨s', hstep⟩ := hreentry
        exact
          ⟨FanReentryModeState.reentry
              (witnessedReentryStateOfStep hstep),
            FanReentryModeStep.reentry_next old s' hstep⟩

end Poincare
