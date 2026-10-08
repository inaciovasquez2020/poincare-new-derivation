import Poincare.GlobalMove32PerpetualWitnessedReentryPredecessorFaceCrossing
import Poincare.GlobalMove32ReentryReturnSourceFaceRigidity

namespace Poincare

/--
A perpetual witnessed-reentry sequence is impossible in the no-degree-four,
no-descent, no-nonself-high branch.

The recurrent crossing theorem supplies a return to an earlier supported-edge
state while the predecessor source face is certified to differ from the
anchor source face.  The exact-three source-face rigidity theorem says the
opposite: equality of the supported-edge state forces equality of the
unordered source-face supports.
-/
theorem
    ClosedTriangulationCore.not_perpetual_witnessedReentry_of_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn :
      TetrahedronVertexOverlapConnected K)
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
    ¬ ∃ sites : Nat → Move32Site,
      sites 0 = start ∧
      (∀ n, (sites n).RealizedIn K) ∧
      (∀ n, (sites n).SharedEdgeExactlyThree K) ∧
      (∀ n, Move32SourceFaceWitnessedReentry K (sites n) (sites (n + 1))) := by

  rintro ⟨sites, hzero, hrealized, hthree, hwitnessed⟩

  obtain ⟨i, k, tau, rho, sigma,
    hgap, hbound,
    htauK, hrhoK, hsigmaK,
    hne,
    haTau, hbTau, hcTau,
    haRho, hbRho, hcRho,
    hdTau, heRho,
    hdSigma, heSigma,
    heNotTau, hdNotRho,
    hsTau, hsRho,
    hreturnEdge,
    htarget,
    hpred⟩ :=
    hcore.exists_finite_recurrent_return_crossing_with_predecessor_sourceFace_ne_of_perpetual_witnessedReentry_of_no_degree_four
      hlinks hconn hNoFour
      sites hrealized hthree hwitnessed

  have hstate :
      sharedSupportedEdgeState hcore (sites i) (hrealized i) =
        sharedSupportedEdgeState hcore (sites (k + 1)) (hrealized (k + 1)) := by
    apply Subtype.ext
    rcases hreturnEdge with hdirect | hreverse
    · simpa [sharedSupportedEdgeState, hdirect.1, hdirect.2]
    · simpa [sharedSupportedEdgeState, hreverse.1, hreverse.2]

  have hsourceEq :=
    hcore.sourceFace_support_eq_of_sharedSupportedEdgeState_eq
      (sites i)
      (sites (k + 1))
      (hrealized i)
      (hthree i)
      (hrealized (k + 1))
      (hthree (k + 1))
      hstate

  exact
    hreturnEdge.elim
      (fun _ => hpred hsourceEq)
      (fun _ => hpred hsourceEq)

end Poincare
