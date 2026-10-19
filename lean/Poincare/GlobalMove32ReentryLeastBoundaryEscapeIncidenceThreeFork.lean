import Poincare.GlobalMove32ReentryLeastBoundaryEscapeNoHigh
import Poincare.GlobalMove32IncidenceThreeCandidate
import Poincare.GlobalMove32IncidenceThreeSplit
import Poincare.GlobalMove32SourceFaceNoHighContradiction
import Poincare.GlobalMove32ReentryFirstNonzeroFailClosed

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
Under the existing fail-closed high-incidence exclusion, the least
left-boundary escape edge has exact tetrahedron incidence three.  The generic
incidence-three constructor therefore produces a realized Move32 candidate on
that exact first-exit edge.  In the no-degree-four branch, the candidate yields
either strict topological `PhiSupport` descent or an explicit represented
source-face obstruction.

This theorem retains the first-exit indices and their inside/outside
classification.  It does not yet resolve the new source-face obstruction into
Move23, further descent, or witnessed reentry.
-/
theorem finite_squareGrid_least_boundary_escape_incidenceThree_descent_or_sourceFace_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
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
    (N : Nat) (hN : 0 < N) :
    let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
    let D := N * 2 ^ (m + 1)
    ∀ (hD : 0 < D)
      (label : Fin D → Fin D → Nat),
      (∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) →
      ∃ j k : Fin D,
        0 < (j : Nat) ∧
        (k : Nat) + 1 = (j : Nat) ∧
        label ⟨0, hD⟩ k ∈
          [(p.crossing.sites p.crossing.anchorIndex).a,
            (p.crossing.sites p.crossing.anchorIndex).b,
            (p.crossing.sites p.crossing.anchorIndex).c,
            (p.crossing.sites p.crossing.anchorIndex).d,
            (p.crossing.sites p.crossing.anchorIndex).e] ∧
        label ⟨0, hD⟩ j ∉
          [(p.crossing.sites p.crossing.anchorIndex).a,
            (p.crossing.sites p.crossing.anchorIndex).b,
            (p.crossing.sites p.crossing.anchorIndex).c,
            (p.crossing.sites p.crossing.anchorIndex).d,
            (p.crossing.sites p.crossing.anchorIndex).e] ∧
        ((∃ K',
            ClosedTriangulationCore K' ∧
            PhiSupport K' < PhiSupport K ∧
            Nonempty
              (triangulationTopologicalGeometricCarrier K ≃ₜ
                triangulationTopologicalGeometricCarrier K')) ∨
          ∃ s : Move32Site,
            s.d = label ⟨0, hD⟩ k ∧
            s.e = label ⟨0, hD⟩ j ∧
            s.RealizedIn K ∧
            s.SharedEdgeExactlyThree K ∧
            ∃ tau ∈ K.tets,
              s.a ∈ tau.verts ∧
              s.b ∈ tau.verts ∧
              s.c ∈ tau.verts) := by
  classical
  dsimp only

  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨j, k, _rho, hjPos, hkSucc, hkInside, hjOutside,
      _hrho, _hkRho, _hjRho, _hnot0, _hnot1, _hnot2, hthree⟩ :=
    finite_squareGrid_least_boundary_escape_edge_incidence_eq_three_of_noHigh_probe
      hcore hlinks hNoFour p H hNoHigh N hN hD label hpositive

  let i0 : Fin D := ⟨0, hD⟩
  let v : Nat := label i0 k
  let x : Nat := label i0 j

  have hkInside' :
      v ∈
        [(p.crossing.sites p.crossing.anchorIndex).a,
          (p.crossing.sites p.crossing.anchorIndex).b,
          (p.crossing.sites p.crossing.anchorIndex).c,
          (p.crossing.sites p.crossing.anchorIndex).d,
          (p.crossing.sites p.crossing.anchorIndex).e] := by
    simpa [v, i0] using hkInside

  have hjOutside' :
      x ∉
        [(p.crossing.sites p.crossing.anchorIndex).a,
          (p.crossing.sites p.crossing.anchorIndex).b,
          (p.crossing.sites p.crossing.anchorIndex).c,
          (p.crossing.sites p.crossing.anchorIndex).d,
          (p.crossing.sites p.crossing.anchorIndex).e] := by
    simpa [x, i0] using hjOutside

  have hvx : v ≠ x := by
    intro hvxEq
    apply hjOutside'
    rw [← hvxEq]
    exact hkInside'

  have hthree' :
      (K.tets.filter
        (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length = 3 := by
    simpa [v, x, i0] using hthree

  obtain ⟨s, hsd, hse, hrealized, hthreeS⟩ :=
    hcore.exists_move32Site_realizedIn_of_edgeIncidence_three
      v x hvx hthree'

  rcases
      exists_closedCore_homeomorphic_PhiSupport_lt_or_sourceFace_obstruction_of_move32_incidence_three
        hcore hNoFour s hrealized hthreeS with
    hdesc | hobstruction

  · refine ⟨j, k, hjPos, hkSucc, hkInside, hjOutside, Or.inl hdesc⟩

  · refine ⟨j, k, hjPos, hkSucc, hkInside, hjOutside, Or.inr ?_⟩
    refine ⟨s, ?_, ?_, hrealized, hthreeS, hobstruction⟩
    · simpa [v, i0] using hsd
    · simpa [x, i0] using hse


/--
The least-boundary first-exit fork has no source-face-obstruction branch
under the same fail-closed high-incidence exclusion.  The obstruction
contradiction is composed here with the geometric fork, so the result is a
strict topological PhiSupport descent on the realized first-exit edge.
-/
theorem finite_squareGrid_least_boundary_escape_incidenceThree_descent_of_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ x y sigma,
          x ≠ y ∧ sigma ∈ K.tets ∧
          x ∈ sigma.verts ∧ y ∈ sigma.verts ∧
          ¬ ((x = s.d ∧ y = s.e) ∨
             (x = s.e ∧ y = s.d)) ∧
          4 ≤ (K.tets.filter
            (fun gamma => decide (x ∈ gamma.verts ∧ y ∈ gamma.verts))).length)
    (N : Nat) (hN : 0 < N) :
    let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
    let D := N * 2 ^ (m + 1)
    ∀ (hD : 0 < D)
      (label : Fin D → Fin D → Nat),
      (∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) →
      ∃ j k : Fin D,
        0 < (j : Nat) ∧
        (k : Nat) + 1 = (j : Nat) ∧
        label ⟨0, hD⟩ k ∈
          [(p.crossing.sites p.crossing.anchorIndex).a,
           (p.crossing.sites p.crossing.anchorIndex).b,
           (p.crossing.sites p.crossing.anchorIndex).c,
           (p.crossing.sites p.crossing.anchorIndex).d,
           (p.crossing.sites p.crossing.anchorIndex).e] ∧
        label ⟨0, hD⟩ j ∉
          [(p.crossing.sites p.crossing.anchorIndex).a,
           (p.crossing.sites p.crossing.anchorIndex).b,
           (p.crossing.sites p.crossing.anchorIndex).c,
           (p.crossing.sites p.crossing.anchorIndex).d,
           (p.crossing.sites p.crossing.anchorIndex).e] ∧
        ∃ K',
          ClosedTriangulationCore K' ∧
          PhiSupport K' < PhiSupport K ∧
          Nonempty
            (triangulationTopologicalGeometricCarrier K ≃ₜ
              triangulationTopologicalGeometricCarrier K') := by
  classical
  dsimp only
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive
  obtain ⟨j, k, hjPos, hkSucc, hkInside, hjOutside, hfork⟩ :=
    finite_squareGrid_least_boundary_escape_incidenceThree_descent_or_sourceFace_probe
      hcore hlinks hNoFour p H hNoHigh N hN hD label hpositive
  rcases hfork with hdesc | ⟨s, hsd, hse, hrealized, _hthreeS, hobstruction⟩
  · exact ⟨j, k, hjPos, hkSucc, hkInside, hjOutside, hdesc⟩
  · exact (move32_sourceFace_obstruction_false_of_noHigh
      hcore hlinks hNoFour s hrealized hobstruction hNoHigh).elim


/--
The no-descent assumption is incompatible with the polygonal null-homotopy
and fail-closed high-incidence exclusion: construct the positive-coordinate
grid at the certificate's dependent dyadic scale, then apply the least-boundary
first-exit descent theorem. This is a conditional contradiction theorem; it
does not remove the need to justify these hypotheses in any global application.
-/
theorem ClosedTriangulationCore.not_noDescent_of_noHigh_sourceFace_start
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hSC : TriangulationRealizationSimplyConnected K)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
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
          x ≠ y ∧ sigma ∈ K.tets ∧
          x ∈ sigma.verts ∧ y ∈ sigma.verts ∧
          ¬ ((x = s.d ∧ y = s.e) ∨
             (x = s.e ∧ y = s.d)) ∧
          4 ≤ (K.tets.filter
            (fun gamma => decide (x ∈ gamma.verts ∧ y ∈ gamma.verts))).length)
    (start : Move32Site)
    (hstartRealized : start.RealizedIn K)
    (hstartThree : start.SharedEdgeExactlyThree K)
    (hstartObstruction :
      ∃ tau ∈ K.tets,
        start.a ∈ tau.verts ∧
        start.b ∈ tau.verts ∧
        start.c ∈ tau.verts) :
    False := by
  obtain ⟨p, hH⟩ :=
    hcore.exists_polygonalLoop_nullHomotopyData_of_no_other_sourceFace_outcome
      hlinks hconn hSC hNoFour hNoDescent hNoHigh
      start hstartRealized hstartThree hstartObstruction
  obtain ⟨H⟩ := hH
  obtain ⟨N, hN, hD, label, _, hpositive⟩ :=
    H.exists_finite_squareGrid_dyadic_refinement_positiveCoordinate_labelling_probe
      (p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex + 1)
  have hdescent :=
    CarrierLoopNullHomotopyData.finite_squareGrid_least_boundary_escape_incidenceThree_descent_of_noHigh
      hcore hlinks hNoFour p H hNoHigh N hN hD label hpositive
  rcases hdescent with ⟨j, k, hj, hk, hinside, houtside, hstrictDescent⟩
  exact hNoDescent hstrictDescent

end CarrierLoopNullHomotopyData
end Poincare
