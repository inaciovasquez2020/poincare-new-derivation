import Poincare.GlobalMove32WitnessedReentryFacePairSeparation
import Poincare.GlobalMove32SharedEdgeThreeTetSaturation
import Mathlib.Tactic

namespace Poincare

theorem
    ClosedTriangulationCore.exists_witnessedReentry_return_crossing_anchor_target_of_sharedSupportedEdgeState_eq
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor prev ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hanchorThree : anchor.SharedEdgeExactlyThree K)
    (hprevRealized : prev.RealizedIn K)
    (hretRealized : ret.RealizedIn K)
    (hstep :
      Move32SourceFaceWitnessedReentry
        K prev ret)
    (hstate :
      sharedSupportedEdgeState
          hcore anchor hanchorRealized =
        sharedSupportedEdgeState
          hcore ret hretRealized) :
    ∃ tau rho sigma,
      tau ∈ K.tets ∧
      rho ∈ K.tets ∧
      sigma ∈ K.tets ∧
      ¬ SameTetVertices tau rho ∧
      prev.a ∈ tau.verts ∧
      prev.b ∈ tau.verts ∧
      prev.c ∈ tau.verts ∧
      prev.a ∈ rho.verts ∧
      prev.b ∈ rho.verts ∧
      prev.c ∈ rho.verts ∧
      ret.d ∈ tau.verts ∧
      ret.e ∈ rho.verts ∧
      ret.d ∈ sigma.verts ∧
      ret.e ∈ sigma.verts ∧
      ret.e ∉ tau.verts ∧
      ret.d ∉ rho.verts ∧
      ¬ SameTetVertices sigma tau ∧
      ¬ SameTetVertices sigma rho ∧
      ((ret.d = anchor.d ∧
        ret.e = anchor.e) ∨
       (ret.d = anchor.e ∧
        ret.e = anchor.d)) ∧
      (SameTetVertices sigma anchor.targetTet₀ ∨
       SameTetVertices sigma anchor.targetTet₁ ∨
       SameTetVertices sigma anchor.targetTet₂) := by
  classical

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

  subst x
  subst y

  have habc :
      [prev.a, prev.b, prev.c].Nodup := by
    have hfive :=
      hcore.move32Site_distinct
        prev
        hprevRealized

    simp only [
      List.nodup_cons,
      List.mem_cons,
      List.not_mem_nil,
      not_or
    ] at hfive ⊢

    aesop

  have hdABC :
      ret.d ≠ prev.a ∧
      ret.d ≠ prev.b ∧
      ret.d ≠ prev.c := by
    simpa only [
      List.mem_cons,
      List.not_mem_nil,
      or_false,
      not_or
    ] using hxABC

  have heABC :
      ret.e ≠ prev.a ∧
      ret.e ≠ prev.b ∧
      ret.e ≠ prev.c := by
    simpa only [
      List.mem_cons,
      List.not_mem_nil,
      or_false,
      not_or
    ] using hyABC

  have htauNodup :
      tau.verts.Nodup :=
    hcore.1 tau htauK

  have hrhoNodup :
      rho.verts.Nodup :=
    hcore.1 rho hrhoK

  obtain
      ⟨tauComplement,
        htauComplement,
        htauUnique⟩ :=
    tau.exists_unique_complement_vertex
      htauNodup
      habc
      haTau
      hbTau
      hcTau

  have hdTauData :
      ret.d ∈ tau.verts ∧
      ret.d ≠ prev.a ∧
      ret.d ≠ prev.b ∧
      ret.d ≠ prev.c :=
    ⟨hxTau,
      hdABC.1,
      hdABC.2.1,
      hdABC.2.2⟩

  have hdTauComplement :
      ret.d = tauComplement :=
    htauUnique
      ret.d
      hdTauData

  have heNotTau :
      ret.e ∉ tau.verts := by
    intro heTau

    have heTauData :
        ret.e ∈ tau.verts ∧
        ret.e ≠ prev.a ∧
        ret.e ≠ prev.b ∧
        ret.e ≠ prev.c :=
      ⟨heTau,
        heABC.1,
        heABC.2.1,
        heABC.2.2⟩

    have heTauComplement :
        ret.e = tauComplement :=
      htauUnique
        ret.e
        heTauData

    exact
      hxy
        (hdTauComplement.trans
          heTauComplement.symm)

  obtain
      ⟨rhoComplement,
        hrhoComplement,
        hrhoUnique⟩ :=
    rho.exists_unique_complement_vertex
      hrhoNodup
      habc
      haRho
      hbRho
      hcRho

  have heRhoData :
      ret.e ∈ rho.verts ∧
      ret.e ≠ prev.a ∧
      ret.e ≠ prev.b ∧
      ret.e ≠ prev.c :=
    ⟨hyRho,
      heABC.1,
      heABC.2.1,
      heABC.2.2⟩

  have heRhoComplement :
      ret.e = rhoComplement :=
    hrhoUnique
      ret.e
      heRhoData

  have hdNotRho :
      ret.d ∉ rho.verts := by
    intro hdRho

    have hdRhoData :
        ret.d ∈ rho.verts ∧
        ret.d ≠ prev.a ∧
        ret.d ≠ prev.b ∧
        ret.d ≠ prev.c :=
      ⟨hdRho,
        hdABC.1,
        hdABC.2.1,
        hdABC.2.2⟩

    have hdRhoComplement :
        ret.d = rhoComplement :=
      hrhoUnique
        ret.d
        hdRhoData

    exact
      hxy
        (hdRhoComplement.trans
          heRhoComplement.symm)

  have hSigmaTau :
      ¬ SameTetVertices sigma tau := by
    intro hsame

    exact
      heNotTau
        ((hsame ret.e).1
          hySigma)

  have hSigmaRho :
      ¬ SameTetVertices sigma rho := by
    intro hsame

    exact
      hdNotRho
        ((hsame ret.d).1
          hxSigma)

  have hkey :
      canonicalEdgeKey anchor.d anchor.e =
        canonicalEdgeKey ret.d ret.e := by
    calc
      canonicalEdgeKey anchor.d anchor.e =
          (sharedSupportedEdgeState
            hcore
            anchor
            hanchorRealized).key :=
        (sharedSupportedEdgeState_key
          hcore
          anchor
          hanchorRealized).symm

      _ =
          (sharedSupportedEdgeState
            hcore
            ret
            hretRealized).key := by
        exact
          congrArg
            (fun q : SupportedEdgeState K =>
              q.key)
            hstate

      _ =
          canonicalEdgeKey ret.d ret.e :=
        sharedSupportedEdgeState_key
          hcore
          ret
          hretRealized

  have hanchorDistinct :
      anchor.d ≠ anchor.e :=
    (hcore.move32_sharedEdge_supported
      anchor
      hanchorRealized).2.2

  have hretDistinct :
      ret.d ≠ ret.e :=
    (hcore.move32_sharedEdge_supported
      ret
      hretRealized).2.2

  have hanchorRet :
      (anchor.d = ret.d ∧
       anchor.e = ret.e) ∨
      (anchor.d = ret.e ∧
       anchor.e = ret.d) :=
    (canonicalEdgeKey_eq_iff
      anchor.d
      anchor.e
      ret.d
      ret.e
      hanchorDistinct
      hretDistinct).1 hkey

  have hretAnchor :
      (ret.d = anchor.d ∧
       ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧
       ret.e = anchor.d) := by
    rcases hanchorRet with
      hdirect | hreverse

    · exact
        Or.inl
          ⟨hdirect.1.symm,
            hdirect.2.symm⟩

    · exact
        Or.inr
          ⟨hreverse.2.symm,
            hreverse.1.symm⟩

  have hAnchorDInSigma :
      anchor.d ∈ sigma.verts := by
    rcases hretAnchor with
      hdirect | hreverse

    · simpa [hdirect.1] using
        hxSigma

    · simpa [hreverse.2] using
        hySigma

  have hAnchorEInSigma :
      anchor.e ∈ sigma.verts := by
    rcases hretAnchor with
      hdirect | hreverse

    · simpa [hdirect.2] using
        hySigma

    · simpa [hreverse.1] using
        hxSigma

  have htarget :
      SameTetVertices sigma anchor.targetTet₀ ∨
      SameTetVertices sigma anchor.targetTet₁ ∨
      SameTetVertices sigma anchor.targetTet₂ :=
    hcore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
      anchor
      hanchorRealized
      hanchorThree
      hsigmaK
      hAnchorDInSigma
      hAnchorEInSigma

  exact
    ⟨tau,
      rho,
      sigma,
      htauK,
      hrhoK,
      hsigmaK,
      hTauRho,
      haTau,
      hbTau,
      hcTau,
      haRho,
      hbRho,
      hcRho,
      hxTau,
      hyRho,
      hxSigma,
      hySigma,
      heNotTau,
      hdNotRho,
      hSigmaTau,
      hSigmaRho,
      hretAnchor,
      htarget⟩

end Poincare
