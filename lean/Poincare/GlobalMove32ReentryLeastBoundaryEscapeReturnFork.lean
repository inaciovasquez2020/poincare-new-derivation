import Poincare.GlobalMove32ReentryLeastBoundaryEscapeStateProgress
import Poincare.GlobalMove32ReentryReturnTargetCompatibility

namespace Poincare
namespace CarrierLoopNullHomotopyData

/--
After the least boundary escape, the forced witnessed-reentry successor either
has a canonical shared-edge key different from the recurrent anchor, or its
retained represented tetrahedron on that returned shared edge is one of the
anchor Move32 target tetrahedra and omits the escaped first-exit vertex.

Thus the two certified state changes sharpen to a three-state alternative:
either the successor is a third shared-edge state, or an immediate return to
the anchor state carries the exact anchor-target compatibility already known
for recurrent returns together with separation from the escaped vertex.  This
theorem does not yet rule out that immediate return.
-/
theorem finite_squareGrid_least_boundary_escape_successor_new_or_anchorTarget_return_probe
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
        canonicalEdgeKey s'.d s'.e ≠ canonicalEdgeKey s.d s.e ∧
        (canonicalEdgeKey s'.d s'.e ≠
            canonicalEdgeKey
              (p.crossing.sites p.crossing.anchorIndex).d
              (p.crossing.sites p.crossing.anchorIndex).e ∨
          ∃ sigma : Tet,
            sigma ∈ K.tets ∧
            (p.crossing.sites p.crossing.anchorIndex).d ∈ sigma.verts ∧
            (p.crossing.sites p.crossing.anchorIndex).e ∈ sigma.verts ∧
            (SameTetVertices sigma
                (p.crossing.sites p.crossing.anchorIndex).targetTet₀ ∨
              SameTetVertices sigma
                (p.crossing.sites p.crossing.anchorIndex).targetTet₁ ∨
              SameTetVertices sigma
                (p.crossing.sites p.crossing.anchorIndex).targetTet₂) ∧
            s.e ∉ sigma.verts) := by
  classical
  dsimp only

  let anchor : Move32Site := p.crossing.sites p.crossing.anchorIndex
  let m := p.crossing.predecessorIndex + 1 - p.crossing.anchorIndex
  let D := N * 2 ^ (m + 1)
  intro hD label hpositive

  obtain ⟨j, k, s, s', hjPos, hkSucc, hkInside, hjOutside,
      hsd, hse, hsRealized, hsThree, hrel, hkeySAnchor, hkeyNext⟩ :=
    finite_squareGrid_least_boundary_escape_two_state_changes_of_no_other_sourceFace_outcome
      hcore hlinks hconn hNoFour p H hNoMove23 hNoDescent hNoHigh
      N hN hD label hpositive

  have hsEOutside :
      s.e ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
    intro hsEmem
    rw [hse] at hsEmem
    exact hjOutside (by simpa [anchor] using hsEmem)

  have hanchorRealized : anchor.RealizedIn K := by
    simpa [anchor] using p.realized p.crossing.anchorIndex

  have hanchorThree : anchor.SharedEdgeExactlyThree K := by
    have h :=
      p.ordered.sharedEdgeExactlyThree
        p.ordered.crossing.anchorIndex
        (by omega)
        (by
          have hg := p.ordered.crossing.gap
          omega)
    rw [p.ordered.traceAt_eq_site] at h
    rw [p.ordered_crossing] at h
    simpa [anchor] using h

  have hplain := hrel.toSourceFaceReentry
  have hs'Realized : s'.RealizedIn K := hplain.1

  have hfork :
      canonicalEdgeKey s'.d s'.e ≠ canonicalEdgeKey anchor.d anchor.e ∨
        ∃ sigma : Tet,
          sigma ∈ K.tets ∧
          anchor.d ∈ sigma.verts ∧
          anchor.e ∈ sigma.verts ∧
          (SameTetVertices sigma anchor.targetTet₀ ∨
            SameTetVertices sigma anchor.targetTet₁ ∨
            SameTetVertices sigma anchor.targetTet₂) ∧
          s.e ∉ sigma.verts := by
    by_cases hreturn :
        canonicalEdgeKey s'.d s'.e = canonicalEdgeKey anchor.d anchor.e
    · right
      have hs'Distinct : s'.d ≠ s'.e :=
        (hcore.move32_sharedEdge_supported s' hs'Realized).2.2
      have hanchorDistinct : anchor.d ≠ anchor.e :=
        (hcore.move32_sharedEdge_supported anchor hanchorRealized).2.2
      have hendpoints :
          (s'.d = anchor.d ∧ s'.e = anchor.e) ∨
          (s'.d = anchor.e ∧ s'.e = anchor.d) :=
        (canonicalEdgeKey_eq_iff
          s'.d s'.e anchor.d anchor.e hs'Distinct hanchorDistinct).1 hreturn

      rcases hrel with
        ⟨tau, rho, x, y, sigma,
          _htauK, _hrhoK, _hne,
          _haTau, _hbTau, _hcTau,
          _haRho, _hbRho, _hcRho,
          _hxTau, _hxABC,
          _hyRho, _hyABC,
          _hxy,
          hsigmaK, hxSigma, hySigma,
          _hnonself,
          hs'd, hs'e,
          _hs'RealizedRel, _hs'Three, _hobstruction⟩

      have hdRetSigma : s'.d ∈ sigma.verts := by
        simpa [hs'd] using hxSigma
      have heRetSigma : s'.e ∈ sigma.verts := by
        simpa [hs'e] using hySigma

      have hdAnchorSigma : anchor.d ∈ sigma.verts := by
        rcases hendpoints with hdirect | hreverse
        · simpa [hdirect.1] using hdRetSigma
        · simpa [hreverse.2] using heRetSigma

      have heAnchorSigma : anchor.e ∈ sigma.verts := by
        rcases hendpoints with hdirect | hreverse
        · simpa [hdirect.2] using heRetSigma
        · simpa [hreverse.1] using hdRetSigma

      have htarget :
          SameTetVertices sigma anchor.targetTet₀ ∨
            SameTetVertices sigma anchor.targetTet₁ ∨
            SameTetVertices sigma anchor.targetTet₂ :=
        hcore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
          anchor hanchorRealized hanchorThree hsigmaK hdAnchorSigma heAnchorSigma

      have hsENotSigma : s.e ∉ sigma.verts := by
        intro hsESigma
        apply hsEOutside
        have htargetKeep := htarget
        rcases htarget with h0 | h1 | h2
        · have hmem : s.e ∈ anchor.targetTet₀.verts :=
            (h0 s.e).1 hsESigma
          simpa [Move32Site.targetTet₀, Tet.verts] using hmem
        · have hmem : s.e ∈ anchor.targetTet₁.verts :=
            (h1 s.e).1 hsESigma
          simpa [Move32Site.targetTet₁, Tet.verts] using hmem
        · have hmem : s.e ∈ anchor.targetTet₂.verts :=
            (h2 s.e).1 hsESigma
          simpa [Move32Site.targetTet₂, Tet.verts] using hmem

      exact ⟨sigma, hsigmaK, hdAnchorSigma, heAnchorSigma, htarget, hsENotSigma⟩
    · exact Or.inl hreturn

  refine ⟨j, k, s, s', hjPos, hkSucc, hkInside, hjOutside,
    hsd, hse, hsRealized, hsThree, hrel, hkeySAnchor, hkeyNext, ?_⟩
  simpa [anchor] using hfork

end CarrierLoopNullHomotopyData
end Poincare
