import Poincare.GlobalMove32ReentryLeastBoundaryEscapeReturnFaceProgressNoMove23
import Poincare.GlobalMove32ReentryImmediateReturnCarrierEscape

namespace Poincare
namespace CarrierLoopNullHomotopyData

/-- In the no-descent/no-high least-boundary branch, an immediate return of
the witnessed-reentry successor to the recurrent anchor edge forces genuine
carrier escape: the predecessor shared-edge endpoint inside the anchor carrier
is an anchor source vertex, and its source face contains a vertex outside the
whole anchor five-vertex carrier. -/
theorem finite_squareGrid_least_boundary_escape_successor_new_or_anchorReturn_carrierEscape_of_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (p : WitnessedReentryPolygonalLoopCertificate K)
    (H : CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop)
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
        canonicalEdgeKey s'.d s'.e ≠ canonicalEdgeKey s.d s.e ∧
        (canonicalEdgeKey s'.d s'.e ≠
            canonicalEdgeKey
              (p.crossing.sites p.crossing.anchorIndex).d
              (p.crossing.sites p.crossing.anchorIndex).e ∨
          (((s'.d = (p.crossing.sites p.crossing.anchorIndex).d ∧
                s'.e = (p.crossing.sites p.crossing.anchorIndex).e) ∨
              (s'.d = (p.crossing.sites p.crossing.anchorIndex).e ∧
                s'.e = (p.crossing.sites p.crossing.anchorIndex).d)) ∧
            (s.d = (p.crossing.sites p.crossing.anchorIndex).a ∨
              s.d = (p.crossing.sites p.crossing.anchorIndex).b ∨
              s.d = (p.crossing.sites p.crossing.anchorIndex).c) ∧
            ∃ q : Nat,
              q ∈ [s.a, s.b, s.c] ∧
              q ∉
                [(p.crossing.sites p.crossing.anchorIndex).a,
                  (p.crossing.sites p.crossing.anchorIndex).b,
                  (p.crossing.sites p.crossing.anchorIndex).c,
                  (p.crossing.sites p.crossing.anchorIndex).d,
                  (p.crossing.sites p.crossing.anchorIndex).e])) := by
  classical
  dsimp only

  let anchor : Move32Site := p.crossing.sites p.crossing.anchorIndex
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨j, k, s, s', hjPos, hkSucc, hkInside, hjOutside,
      hsd, hse, hsRealized, hsThree, hrel, hkeySAnchor, hkeyNext, hfork⟩ :=
    finite_squareGrid_least_boundary_escape_successor_new_or_anchorReturn_sourceFace_ne_of_noDescent_noHigh
      hcore hlinks hconn hNoFour p H hNoDescent hNoHigh
      N hN hD label hpositive

  refine ⟨j, k, s, s', hjPos, hkSucc, hkInside, hjOutside,
    hsd, hse, hsRealized, hsThree, hrel, hkeySAnchor, hkeyNext, ?_⟩

  rcases hfork with hnew | hreturnData
  · exact Or.inl hnew
  · rcases hreturnData with
      ⟨⟨hreturn, hsourceNe⟩, _sigma, _hsigmaK, _hdSigma, _heSigma, _htarget⟩

    have hanchorRealized : anchor.RealizedIn K := by
      simpa [anchor] using p.realized p.crossing.anchorIndex

    have hsDInside :
        s.d ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
      rw [hsd]
      simpa [anchor] using hkInside

    obtain ⟨hsDClass, q, hqSource, hqOutside⟩ :=
      hcore.exists_anchorSource_endpoint_and_new_source_vertex_of_witnessedReentry_return_edge
        hlinks hNoFour anchor s s' hanchorRealized hsRealized hrel
        hreturn hsDInside hsourceNe

    right
    refine ⟨?_, ?_, q, hqSource, ?_⟩
    · simpa [anchor] using hreturn
    · simpa [anchor] using hsDClass
    · simpa [anchor] using hqOutside

end CarrierLoopNullHomotopyData
end Poincare
