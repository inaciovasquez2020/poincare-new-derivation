import Poincare.GlobalMove32ReentryPolygonalLoopNullHomotopyFailClosed
import Poincare.GlobalMove32ReentryDyadicGridVertices
import Poincare.GlobalMove32ReentryFirstNonzeroExhaustiveFork

namespace Poincare

/--
Under the fail-closed source-face hypotheses, first choose the ordered recurrent
polygonal-loop certificate and its null-homotopy.  Then refine at one dyadic
level beyond that certificate's own ordered-transition count, construct the
strict-positive finite cell labelling at that dependent scale, and feed it
into the existing exhaustive first-ear fork.

This closes the dependency between the existential recurrent certificate and
the refinement depth required by the first-nonzero boundary analysis.  It does
not eliminate the cancellation or two-sided target-transition branches and it
does not assert `Poincare.JIID`.
-/
theorem ClosedTriangulationCore.exists_first_nonzero_anchor_firstEar_exhaustiveFork_of_no_other_sourceFace_outcome
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
                    ∃ rho : Tet,
                      rho ∈ K.tets ∧
                      rho ≠ tau ∧
                      label ⟨0, hD⟩ ⟨0, hD⟩ ∈ rho.verts ∧
                      label ⟨0, hD⟩ ⟨1, hDtwo⟩ ∈ rho.verts ∧
                      (((SameTetVertices tau
                            (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
                          label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                            (p.crossing.sites p.crossing.anchorIndex).b) ∨
                        (SameTetVertices tau
                            (p.crossing.sites p.crossing.anchorIndex).targetTet₂ ∧
                          label ⟨0, hD⟩ ⟨1, hDtwo⟩ =
                            (p.crossing.sites p.crossing.anchorIndex).a)) ∧
                        (((((p.crossing.sites p.crossing.anchorIndex).d ∈ rho.verts ∧
                                (p.crossing.sites p.crossing.anchorIndex).e ∈ rho.verts)) ∧
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
                          (((((p.crossing.sites p.crossing.anchorIndex).d ∈ rho.verts ∧
                                  (p.crossing.sites p.crossing.anchorIndex).e ∉ rho.verts) ∨
                                ((p.crossing.sites p.crossing.anchorIndex).e ∈ rho.verts ∧
                                  (p.crossing.sites p.crossing.anchorIndex).d ∉ rho.verts)) ∧
                              ¬ SameTetVertices rho
                                  (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∧
                              ¬ SameTetVertices rho
                                  (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∧
                              ¬ SameTetVertices rho
                                  (p.crossing.sites p.crossing.anchorIndex).targetTet₂) ∧
                            ∃ v x : Nat,
                              ((v = (p.crossing.sites p.crossing.anchorIndex).b ∧
                                  x = (p.crossing.sites p.crossing.anchorIndex).d) ∨
                                (v = (p.crossing.sites p.crossing.anchorIndex).b ∧
                                  x = (p.crossing.sites p.crossing.anchorIndex).e) ∨
                                (v = (p.crossing.sites p.crossing.anchorIndex).a ∧
                                  x = (p.crossing.sites p.crossing.anchorIndex).d) ∨
                                (v = (p.crossing.sites p.crossing.anchorIndex).a ∧
                                  x = (p.crossing.sites p.crossing.anchorIndex).e)) ∧
                              v ∈ rho.verts ∧
                              x ∈ rho.verts ∧
                              ((K.tets.filter
                                  (fun sigma =>
                                    v ∈ sigma.verts ∧ x ∈ sigma.verts)).length = 3 ∨
                                4 ≤
                                  (K.tets.filter
                                    (fun sigma =>
                                      v ∈ sigma.verts ∧ x ∈ sigma.verts)).length))))) := by
  obtain ⟨p, hH⟩ :=
    hcore.exists_polygonalLoop_nullHomotopyData_of_no_other_sourceFace_outcome
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

  obtain ⟨H⟩ := hH

  obtain ⟨N, hN, hD, label, _, hpositive⟩ :=
    H.exists_finite_squareGrid_dyadic_refinement_positiveCoordinate_labelling_probe
      (p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex + 1)

  obtain ⟨hDtwo, tau, htau, hlabel0Tau, hfork⟩ :=
    H.finite_squareGrid_first_nonzero_anchor_firstEar_exhaustiveFork_probe
      hcore p N hN hD label hpositive

  refine ⟨p, H, N, hN, ?_⟩
  dsimp only
  exact ⟨hD, label, hpositive, hDtwo, tau, htau, hlabel0Tau, hfork⟩

end Poincare
