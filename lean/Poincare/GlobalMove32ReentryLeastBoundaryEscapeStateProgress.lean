import Poincare.GlobalMove32ReentryLeastBoundaryEscapeReentry
import Poincare.GlobalMove32SupportedEdgeState

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
Under the fail-closed hypotheses, the least boundary escape produces a shared
edge whose canonical unordered-edge key differs from the recurrent anchor
shared edge.  Its forced witnessed-reentry successor changes the canonical
shared-edge key once more.

This is a finite-state progress certificate only.  It does not yet prove that
the resulting state can never recur later in the sequence.
-/
theorem finite_squareGrid_least_boundary_escape_two_state_changes_of_no_other_sourceFace_outcome
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
        Move32SourceFaceWitnessedReentry K s s' ∧
        canonicalEdgeKey s.d s.e ≠
          canonicalEdgeKey
            (p.crossing.sites p.crossing.anchorIndex).d
            (p.crossing.sites p.crossing.anchorIndex).e ∧
        canonicalEdgeKey s'.d s'.e ≠ canonicalEdgeKey s.d s.e := by
  classical
  dsimp only

  let anchor : Move32Site := p.crossing.sites p.crossing.anchorIndex
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨j, k, s, s', hjPos, hkSucc, hkInside, hjOutside,
      hsd, hse, hsRealized, hsThree, hrel⟩ :=
    finite_squareGrid_least_boundary_escape_witnessedReentry_of_no_other_sourceFace_outcome
      hcore hlinks hconn hNoFour p H hNoMove23 hNoDescent hNoHigh
      N hN hD label hpositive

  have hjOutside' :
      label ⟨0, hD⟩ j ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
    simpa [anchor] using hjOutside

  have hsEOutside : s.e ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
    rw [hse]
    exact hjOutside'

  have hnonAnchor :
      ¬ ((s.d = anchor.d ∧ s.e = anchor.e) ∨
         (s.d = anchor.e ∧ s.e = anchor.d)) := by
    intro hself
    apply hsEOutside
    rcases hself with hde | hed
    · rw [hde.2]
      simp
    · rw [hed.2]
      simp

  have hanchorRealized : anchor.RealizedIn K := by
    simpa [anchor] using p.realized p.crossing.anchorIndex

  have hsDistinct : s.d ≠ s.e :=
    (hcore.move32_sharedEdge_supported s hsRealized).2.2

  have hanchorDistinct : anchor.d ≠ anchor.e :=
    (hcore.move32_sharedEdge_supported anchor hanchorRealized).2.2

  have hkeyAnchor :
      canonicalEdgeKey s.d s.e ≠ canonicalEdgeKey anchor.d anchor.e := by
    intro hkey
    exact hnonAnchor
      ((canonicalEdgeKey_eq_iff
        s.d s.e anchor.d anchor.e hsDistinct hanchorDistinct).1 hkey)

  have hplain := hrel.toSourceFaceReentry
  have hs'Realized : s'.RealizedIn K := hplain.1
  have hs'Distinct : s'.d ≠ s'.e :=
    (hcore.move32_sharedEdge_supported s' hs'Realized).2.2

  have hkeyNext :
      canonicalEdgeKey s'.d s'.e ≠ canonicalEdgeKey s.d s.e := by
    intro hkey
    exact hplain.2.2.2
      ((canonicalEdgeKey_eq_iff
        s'.d s'.e s.d s.e hs'Distinct hsDistinct).1 hkey)

  refine ⟨j, k, s, s', hjPos, hkSucc, hkInside, hjOutside,
    hsd, hse, hsRealized, hsThree, hrel, ?_, hkeyNext⟩
  simpa [anchor] using hkeyAnchor

end CarrierLoopNullHomotopyData
end Poincare
