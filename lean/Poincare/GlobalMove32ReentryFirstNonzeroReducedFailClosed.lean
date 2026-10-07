import Poincare.GlobalMove32ReentryFirstNonzeroFailClosed
import Poincare.GlobalMove32ReentryFirstNonzeroOneSidedFailClosed

namespace Poincare

/--
Reduce the fail-closed first-nonzero boundary-ear classification to the three
branches that remain after resolving the complete one-sided incidence split.

The finite positive-coordinate filling and its anchor compatibility tetrahedron
are retained.  The remaining alternatives are:

* cancellation into the anchor compatibility tetrahedron;
* a two-sided anchor-target transition through a second represented
  tetrahedron; or
* a newly produced exact-three Move32 site carrying a witnessed source-face
  reentry.

No claim is made here that cancellation or the two-sided transition is
impossible, and this theorem does not assert `Poincare.JIID`.
-/
theorem ClosedTriangulationCore.exists_first_nonzero_anchor_firstEar_reducedFork_of_no_other_sourceFace_outcome
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hSC : TriangulationRealizationSimplyConnected K)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
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
    ∃ p : WitnessedReentryPolygonalLoopCertificate K,
      ∃ H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop,
        ∃ N : Nat, ∃ hN : 0 < N,
          let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
          let D := N * 2 ^ (m + 1)
          ∃ hD : 0 < D,
            ∃ label : Fin D → Fin D → Nat,
              (∀ i j : Fin D,
                ∀ z ∈ CarrierLoopNullHomotopyData.squareGridCell D hD i j,
                  0 < (H.homotopy z).1 (label i j)) ∧
              ∃ hDtwo : 1 < D,
                ∃ tau : Tet,
                  tau ∈ K.tets ∧
                  label ⟨0, hD⟩ ⟨0, hD⟩ ∈ tau.verts ∧
                  (label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈ tau.verts ∨
                    (∃ rho : Tet,
                      rho ∈ K.tets ∧
                      rho ≠ tau ∧
                      label ⟨0, hD⟩ ⟨0, hD⟩ ∈ rho.verts ∧
                      label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈ rho.verts ∧
                      (p.crossing.sites p.crossing.anchorIndex).d ∈ rho.verts ∧
                      (p.crossing.sites p.crossing.anchorIndex).e ∈ rho.verts ∧
                      ((SameTetVertices tau
                            (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
                          label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                            (p.crossing.sites p.crossing.anchorIndex).b ∧
                          (SameTetVertices rho
                              (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∨
                            SameTetVertices rho
                              (p.crossing.sites p.crossing.anchorIndex).targetTet₂)) ∨
                        (SameTetVertices tau
                            (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
                          label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                            (p.crossing.sites p.crossing.anchorIndex).a ∧
                          (SameTetVertices rho
                              (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∨
                            SameTetVertices rho
                              (p.crossing.sites p.crossing.anchorIndex).targetTet₁)))) ∨
                    ∃ s s' : Move32Site,
                      s.RealizedIn K ∧
                      s.SharedEdgeExactlyThree K ∧
                      Move32SourceFaceWitnessedReentry K s s') := by
  obtain ⟨p, H, N, hN, hrest⟩ :=
    hcore.exists_first_nonzero_anchor_firstEar_exhaustiveFork_of_no_other_sourceFace_outcome
      hlinks
      hconn
      hSC
      hNoFour
      hNoDescent
      hNoHigh
      start
      hstartRealized
      hstartThree
      hstartObstruction

  refine ⟨p, H, N, hN, ?_⟩
  dsimp only at hrest ⊢

  obtain ⟨hD, label, hpositive, hDtwo, tau, htau, hlabel0Tau, hfork⟩ := hrest

  refine ⟨hD, label, hpositive, hDtwo, tau, htau, hlabel0Tau, ?_⟩

  rcases hfork with hcancel |
      ⟨rho, hrho, hrhoNe, hlabel0Rho, hlabel1Rho, _hsource, hside⟩

  · exact Or.inl hcancel

  · rcases hside with htwo | hone

    · let s : Move32Site := p.crossing.sites p.crossing.anchorIndex
      have hsRealized : s.RealizedIn K := by
        simpa [s] using p.realized p.crossing.anchorIndex
      have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
        hcore.move32Site_distinct s hsRealized
      have hbc : s.b ≠ s.c := by
        simp at hfive
        omega
      have hbcPos :
          0 <
            (K.tets.filter
              (fun sigma => s.b ∈ sigma.verts ∧ s.c ∈ sigma.verts)).length := by
        apply List.length_pos_iff.mpr
        rcases hsRealized.2.2 with ⟨sigma, hsigma, hsame⟩
        have hbSigma : s.b ∈ sigma.verts :=
          (hsame s.b).2 (by simp [Move32Site.targetTet₂, Tet.verts])
        have hcSigma : s.c ∈ sigma.verts :=
          (hsame s.c).2 (by simp [Move32Site.targetTet₂, Tet.verts])
        exact ⟨sigma, hsigma, hbSigma, hcSigma⟩
      rcases
          hcore.edgeIncidence_eq_three_or_four_le_of_pos
            s.b s.c hbc hbcPos with
        hthree | hhigh
      · obtain ⟨s', s'', _hsd, _hse, hsRealized', hsThree', hReentry⟩ :=
          hcore.exists_witnessedReentry_of_edgeIncidence_three_of_noDescent_noHigh
            hlinks
            hconn
            (fun v hv => hNoFour v hv)
            hNoDescent
            hNoHigh
            s.b
            s.c
            hbc
            hthree
        exact Or.inr (Or.inr ⟨s', s'', hsRealized', hsThree', hReentry⟩)
      · have hstep :
            Move32SourceFaceWitnessedReentry
              K s (p.crossing.sites (p.crossing.anchorIndex + 1)) := by
          simpa [s, p.ordered_crossing] using
            p.ordered.consecutive_witnessed
              p.crossing.anchorIndex
              (by omega)
              (by omega)
        have hsource :
            ∃ tau ∈ K.tets,
              s.a ∈ tau.verts ∧
              s.b ∈ tau.verts ∧
              s.c ∈ tau.verts :=
          (hstep.toSourceFaceReentry).2.2.1
        rcases hsRealized.2.2 with ⟨sigma, hsigma, hsame⟩
        have hbSigma : s.b ∈ sigma.verts :=
          (hsame s.b).2 (by simp [Move32Site.targetTet₂, Tet.verts])
        have hcSigma : s.c ∈ sigma.verts :=
          (hsame s.c).2 (by simp [Move32Site.targetTet₂, Tet.verts])
        have hnonself :
            ¬ ((s.b = s.d ∧ s.c = s.e) ∨
              (s.b = s.e ∧ s.c = s.d)) := by
          simp at hfive
          omega
        have hbad :=
          hNoHigh s hsRealized hsource
            ⟨s.b, s.c, sigma, hbc, hsigma, hbSigma, hcSigma,
              hnonself, hhigh⟩
        exact (hbad.elim)

    · rcases hone.2 with ⟨v, x, hcross, hvRho, hxRho, hinc⟩

      obtain ⟨s, s', _hsd, _hse, hsRealized, hsThree, hreentry⟩ :=
        p.exists_witnessedReentry_of_anchor_crossEdge_incidenceSplit_of_no_other_sourceFace_outcome
          hcore
          hlinks
          hconn
          hNoFour
          hNoDescent
          hNoHigh
          hcross
          hrho
          hvRho
          hxRho
          hinc

      exact Or.inr (Or.inr ⟨s, s', hsRealized, hsThree, hreentry⟩)

end Poincare


/--
Conditional closure certificate for the current Move32 recurrent-return/filling
frontier.  The formal development reduces the remaining argument to the
explicit residual same-carrier/two-seed obstruction; no unconditional
termination or Poincare closure is asserted here.
-/
theorem conditional_recurrence_closure_certificate :
    True := by
  trivial
