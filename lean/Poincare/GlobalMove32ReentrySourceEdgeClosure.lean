import Poincare.GlobalMove32PerpetualWitnessedReentryRecurrentCrossing
import Poincare.GlobalMove32SourceFaceSourceEdgeHigh
import Mathlib.Tactic

namespace Poincare

/--
The recurrent-crossing branch is already contradictory under the existing
no-degree-four/no-high hypotheses.

The recurrent crossing certificate contains tetrahedra tau and rho
representing the predecessor site's source face. Therefore the predecessor
itself is a represented Move32 source-face obstruction. The source-edge
theorem then forces its (a,b) source edge to have incidence at least four.
That edge is not the predecessor's complementary (d,e) edge, so hNoHigh
rules it out.

This avoids identifying tau or rho with the predecessor's canonical
sourceTet0/sourceTet1; only vertex-set containment is needed.
-/
theorem ClosedTriangulationCore.not_perpetual_witnessedReentry_of_noDescent_noHigh_sourceEdge
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ x y sigma,
          x ≠ y ∧
          sigma ∈ K.tets ∧
          x ∈ sigma.verts ∧
          y ∈ sigma.verts ∧
          ¬ ((x = s.d ∧ y = s.e) ∨
             (x = s.e ∧ y = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (x ∈ gamma.verts ∧
                   y ∈ gamma.verts))).length)
    (start : Move32Site)
    (hstartRealized : start.RealizedIn K)
    (hstartThree : start.SharedEdgeExactlyThree K)
    (hstartObstruction :
      ∃ tau ∈ K.tets,
        start.a ∈ tau.verts ∧
        start.b ∈ tau.verts ∧
        start.c ∈ tau.verts) :
    False := by
  obtain ⟨sites, _hzero, hrealized, hthree, _hobstruction, hwitnessed⟩ :=
    hcore.exists_perpetual_witnessedReentry_of_no_other_sourceFace_outcome
      hlinks
      hconn
      hNoFour
      (by
        intro s hsRealized hsObstruction hmove23
        exact
          hNoHigh s hsRealized hsObstruction
            (hcore.exists_nonself_complementEdge_high_of_move32_sourceFace_obstruction_of_no_degree_four
              hlinks hNoFour s hsRealized hsObstruction))
      hNoDescent
      hNoHigh
      start
      hstartRealized
      hstartThree
      hstartObstruction

  obtain ⟨i, k, hgap, hbound, hstate, hstep, _⟩ :=
    hcore.exists_recurrent_returnSigma_target_of_perpetual_witnessedReentry
      sites hrealized hthree hwitnessed

  obtain ⟨tau, rho, sigma, hconfig⟩ :=
    hcore.exists_witnessedReentry_return_crossing_anchor_target_of_sharedSupportedEdgeState_eq
      (sites i) (sites k) (sites (k + 1))
      (hrealized i) (hthree i) (hrealized k) (hrealized (k + 1))
      hstep hstate

  rcases hconfig with
    ⟨htau, hrho, hsigma, htaurho,
      haTau, hbTau, hcTau,
      haRho, hbRho, hcRho,
      hdTau, heRho, hdSigma, heSigma,
      heNotTau, hdNotRho, hSigmaTau, hSigmaRho,
      hreturn, htarget⟩

  have hpredObstruction :
      ∃ theta ∈ K.tets,
        (sites k).a ∈ theta.verts ∧
        (sites k).b ∈ theta.verts ∧
        (sites k).c ∈ theta.verts :=
    ⟨tau, htau, haTau, hbTau, hcTau⟩

  have hsourceHigh :=
    hcore.move32_sourceEdge_ab_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
      hlinks hNoFour (sites k) (hrealized k) hpredObstruction

  have hsourceDistinct :=
    hcore.move32Site_distinct (sites k) (hrealized k)

  have hab : (sites k).a ≠ (sites k).b := by
    simp at hsourceDistinct
    aesop

  have hnonself :
      ¬ (((sites k).a = (sites k).d ∧ (sites k).b = (sites k).e) ∨
         ((sites k).a = (sites k).e ∧ (sites k).b = (sites k).d)) := by
    simp at hsourceDistinct
    aesop

  have hsourceHighDecide :
      4 ≤
        (K.tets.filter
          (fun gamma =>
            decide
              ((sites k).a ∈ gamma.verts ∧
               (sites k).b ∈ gamma.verts))).length := by
    simpa using hsourceHigh

  exact
    (hNoHigh (sites k) (hrealized k) hpredObstruction)
      ⟨(sites k).a, (sites k).b, tau,
        hab, htau, haTau, hbTau, hnonself, hsourceHighDecide⟩

end Poincare
