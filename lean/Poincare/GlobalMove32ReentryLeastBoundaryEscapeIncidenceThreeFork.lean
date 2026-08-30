import Poincare.GlobalMove32ReentryLeastBoundaryEscapeNoHigh
import Poincare.GlobalMove32IncidenceThreeCandidate
import Poincare.GlobalMove32IncidenceThreeSplit

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

end CarrierLoopNullHomotopyData
end Poincare
