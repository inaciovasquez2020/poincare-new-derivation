import Poincare.GlobalMove32SharedEdgeThreeTetSaturation
import Mathlib.Tactic

namespace Poincare

/--
If a witnessed source-face reentry lands on a Move32 shared-edge state equal
to the canonical shared-edge state of an earlier realized incidence-three
Move32 site, then the retained represented tetrahedron `sigma` from that
reentry contains the earlier shared edge and is therefore one of the earlier
site's three target tetrahedra up to `SameTetVertices`.

This is a return-compatibility theorem only.  It does not assert that such a
return is impossible.
-/
theorem
    ClosedTriangulationCore.exists_returnSigma_same_anchor_target_of_witnessedReentry_of_sharedSupportedEdgeState_eq
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor prev ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hanchorThree : anchor.SharedEdgeExactlyThree K)
    (hretRealized : ret.RealizedIn K)
    (hstep :
      Move32SourceFaceWitnessedReentry
        K
        prev
        ret)
    (hstate :
      sharedSupportedEdgeState
          hcore
          ret
          hretRealized =
        sharedSupportedEdgeState
          hcore
          anchor
          hanchorRealized) :
    ∃ sigma,
      sigma ∈ K.tets ∧
      anchor.d ∈ sigma.verts ∧
      anchor.e ∈ sigma.verts ∧
      (SameTetVertices sigma anchor.targetTet₀ ∨
        SameTetVertices sigma anchor.targetTet₁ ∨
        SameTetVertices sigma anchor.targetTet₂) := by
  classical

  have hkey :
      canonicalEdgeKey ret.d ret.e =
        canonicalEdgeKey anchor.d anchor.e := by
    calc
      canonicalEdgeKey ret.d ret.e =
          (sharedSupportedEdgeState
            hcore
            ret
            hretRealized).key :=
        (sharedSupportedEdgeState_key
          hcore
          ret
          hretRealized).symm

      _ =
          (sharedSupportedEdgeState
            hcore
            anchor
            hanchorRealized).key := by
        exact
          congrArg
            (fun q : SupportedEdgeState K =>
              q.key)
            hstate

      _ =
          canonicalEdgeKey anchor.d anchor.e :=
        sharedSupportedEdgeState_key
          hcore
          anchor
          hanchorRealized

  have hretDistinct :
      ret.d ≠ ret.e :=
    (hcore.move32_sharedEdge_supported
      ret
      hretRealized).2.2

  have hanchorDistinct :
      anchor.d ≠ anchor.e :=
    (hcore.move32_sharedEdge_supported
      anchor
      hanchorRealized).2.2

  have hendpoints :
      (ret.d = anchor.d ∧
       ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧
       ret.e = anchor.d) :=
    (canonicalEdgeKey_eq_iff
      ret.d
      ret.e
      anchor.d
      anchor.e
      hretDistinct
      hanchorDistinct).1 hkey

  rcases hstep with
    ⟨tau,
      rho,
      x,
      y,
      sigma,
      htauK,
      hrhoK,
      hTauRho,
      haTau,
      hbTau,
      hcTau,
      haRho,
      hbRho,
      hcRho,
      hxTau,
      hxABC,
      hyRho,
      hyABC,
      hxy,
      hsigmaK,
      hxSigma,
      hySigma,
      hnonself,
      hretD,
      hretE,
      hrealizedStep,
      hthreeStep,
      hobstructionStep⟩

  have hdRetSigma :
      ret.d ∈ sigma.verts := by
    simpa [hretD] using hxSigma

  have heRetSigma :
      ret.e ∈ sigma.verts := by
    simpa [hretE] using hySigma

  have hdAnchorSigma :
      anchor.d ∈ sigma.verts := by
    rcases hendpoints with
      hdirect | hreverse

    · simpa [hdirect.1] using
        hdRetSigma

    · simpa [hreverse.2] using
        heRetSigma

  have heAnchorSigma :
      anchor.e ∈ sigma.verts := by
    rcases hendpoints with
      hdirect | hreverse

    · simpa [hdirect.2] using
        heRetSigma

    · simpa [hreverse.1] using
        hdRetSigma

  have htarget :
      SameTetVertices sigma anchor.targetTet₀ ∨
        SameTetVertices sigma anchor.targetTet₁ ∨
          SameTetVertices sigma anchor.targetTet₂ :=
    hcore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
      anchor
      hanchorRealized
      hanchorThree
      hsigmaK
      hdAnchorSigma
      heAnchorSigma

  exact
    ⟨sigma,
      hsigmaK,
      hdAnchorSigma,
      heAnchorSigma,
      htarget⟩

end Poincare
