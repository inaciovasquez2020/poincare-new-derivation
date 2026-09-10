import Poincare.GlobalMove32ReentryFirstNonzeroNoHigh
import Poincare.GlobalMove32ReentryFirstNonzeroIncidenceThreeDescentFork
import Poincare.GlobalMove32WitnessedSourceFaceReentry
import Poincare.GlobalMove32SourceFaceLegalMove23High

namespace Poincare

/--
Under the fail-closed source-face hypotheses, a represented one-sided first-ear
anchor cross edge whose incidence is known to be `= 3 ∨ ≥ 4` necessarily
produces a witnessed source-face reentry.

The high-incidence half is first eliminated by `hNoHigh`.  The remaining
exact-incidence-three cross edge is converted to a realized exact-three Move32
source-face obstruction.  The certified source-face classification already
absorbs aligned legal Move23 output into the nonself high-incidence branch, so
excluding descent and high incidence leaves witnessed reentry.

This theorem resolves only the one-sided first-ear branch.  It does not
eliminate cancellation or the two-sided target-transition branch.
-/
theorem WitnessedReentryPolygonalLoopCertificate.exists_witnessedReentry_of_anchor_crossEdge_incidenceSplit_of_no_other_sourceFace_outcome
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
    (p : WitnessedReentryPolygonalLoopCertificate K)
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
    {v x : Nat}
    (hcross :
      (v = (p.crossing.sites p.crossing.anchorIndex).b ∧
          x = (p.crossing.sites p.crossing.anchorIndex).d) ∨
        (v = (p.crossing.sites p.crossing.anchorIndex).b ∧
          x = (p.crossing.sites p.crossing.anchorIndex).e) ∨
        (v = (p.crossing.sites p.crossing.anchorIndex).a ∧
          x = (p.crossing.sites p.crossing.anchorIndex).d) ∨
        (v = (p.crossing.sites p.crossing.anchorIndex).a ∧
          x = (p.crossing.sites p.crossing.anchorIndex).e))
    {rho : Tet}
    (hrho : rho ∈ K.tets)
    (hvRho : v ∈ rho.verts)
    (hxRho : x ∈ rho.verts)
    (hinc :
      (K.tets.filter
          (fun sigma => v ∈ sigma.verts ∧ x ∈ sigma.verts)).length = 3 ∨
        4 ≤
          (K.tets.filter
            (fun sigma => v ∈ sigma.verts ∧ x ∈ sigma.verts)).length) :
    ∃ s s' : Move32Site,
      s.d = v ∧
      s.e = x ∧
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      Move32SourceFaceWitnessedReentry K s s' := by
  have hthree :
      (K.tets.filter
          (fun sigma => v ∈ sigma.verts ∧ x ∈ sigma.verts)).length = 3 :=
    WitnessedReentryPolygonalLoopCertificate.anchor_crossEdge_incidence_eq_three_of_split_of_noHigh
      hcore p hNoHigh hcross hrho hvRho hxRho hinc

  have hanchorRealized :
      (p.crossing.sites p.crossing.anchorIndex).RealizedIn K :=
    p.realized p.crossing.anchorIndex

  rcases
      hcore.exists_descent_or_sourceFace_obstruction_of_firstEar_crossEdge_incidence_three
        hNoFour
        (p.crossing.sites p.crossing.anchorIndex)
        hanchorRealized
        v
        x
        hcross
        hthree with
    hdesc | ⟨s, hsd, hse, hsRealized, hsThree, hsObstruction⟩

  · exact (hNoDescent hdesc).elim

  · rcases
        hcore.exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
          hlinks hconn hNoFour s hsRealized hsObstruction with
      hdesc | hhigh | hreentry

    · exact (hNoDescent hdesc).elim
    · exact (hNoHigh s hsRealized hsObstruction hhigh).elim
    · rcases hreentry with ⟨s', hrel⟩
      exact ⟨s, s', hsd, hse, hsRealized, hsThree, hrel⟩

end Poincare
