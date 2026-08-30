import Poincare.GlobalMove32ReentryLeastBoundaryEscapeIncidenceThreeFork
import Poincare.GlobalMove32WitnessedSourceFaceReentry

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
Under the same fail-closed hypotheses used by the perpetual witnessed-reentry
builder, the least left-boundary escape cannot terminate in descent, a matching
legal Move23, or a nonself high-incidence edge.  Hence the exact-incidence-three
Move32 candidate carried by the first-exit edge is forced into witnessed
source-face reentry.

The theorem retains the least-exit indices and identifies the new Move32 shared
edge with the actual predecessor/escape boundary labels.
-/
theorem finite_squareGrid_least_boundary_escape_witnessedReentry_of_no_other_sourceFace_outcome
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
    (hNoMove23 :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ m : Move23Site,
          m.a = s.a ∧
          m.b = s.b ∧
          m.c = s.c ∧
          m.LegalIn K)
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
    (N : Nat) (hN : 0 < N) :
    let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
    let D := N * 2 ^ (m + 1)
    ∀ (hD : 0 < D)
      (label : Fin D → Fin D → Nat),
      (∀ i j : Fin D,
        ∀ z ∈ squareGridCell D hD i j,
          0 < (H.homotopy z).1 (label i j)) →
      ∃ j k : Fin D, ∃ s s' : Move32Site,
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
        s.d = label ⟨0, hD⟩ k ∧
        s.e = label ⟨0, hD⟩ j ∧
        s.RealizedIn K ∧
        s.SharedEdgeExactlyThree K ∧
        Move32SourceFaceWitnessedReentry K s s' := by
  dsimp only

  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨j, k, hjPos, hkSucc, hkInside, hjOutside, hfork⟩ :=
    finite_squareGrid_least_boundary_escape_incidenceThree_descent_or_sourceFace_probe
      hcore hlinks hNoFour p H hNoHigh N hN hD label hpositive

  rcases hfork with hdesc | hsource

  · exact (hNoDescent hdesc).elim

  · rcases hsource with
      ⟨s, hsd, hse, hrealized, hthree, hobstruction⟩

    rcases
        hcore.exists_legal_move23_or_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
          hlinks hconn hNoFour s hrealized hobstruction with
      hmove23 | hdesc | hhigh | hreentry

    · exact (hNoMove23 s hrealized hobstruction hmove23).elim

    · exact (hNoDescent hdesc).elim

    · exact (hNoHigh s hrealized hobstruction hhigh).elim

    · rcases hreentry with ⟨s', hrel⟩
      exact
        ⟨j, k, s, s',
          hjPos, hkSucc, hkInside, hjOutside,
          hsd, hse, hrealized, hthree, hrel⟩

end CarrierLoopNullHomotopyData
end Poincare
