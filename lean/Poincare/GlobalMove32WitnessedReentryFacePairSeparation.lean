import Poincare.GlobalMove32WitnessedFiniteRecurrenceReturn
import Mathlib.Tactic

namespace Poincare

/--
For an actual witnessed Move32 source-face reentry, the represented
complementary-edge tetrahedron `sigma` is distinct, up to
`SameTetVertices`, from both tetrahedra `tau` and `rho` across the old
source face.

More precisely, for the same witnesses carried by the reentry relation,
the complementary vertex from `rho` is absent from `tau`, and conversely.
No recurrence, termination, or descent conclusion is used here.
-/
theorem
    ClosedTriangulationCore.exists_witnessedReentry_facePair_sigma_separated
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s s' : Move32Site)
    (hrealized : s.RealizedIn K)
    (hstep :
      Move32SourceFaceWitnessedReentry K s s') :
    ∃ tau rho x y sigma,
      tau ∈ K.tets ∧
      rho ∈ K.tets ∧
      sigma ∈ K.tets ∧
      x ∈ tau.verts ∧
      y ∈ rho.verts ∧
      x ∈ sigma.verts ∧
      y ∈ sigma.verts ∧
      y ∉ tau.verts ∧
      x ∉ rho.verts ∧
      ¬ SameTetVertices tau rho ∧
      ¬ SameTetVertices sigma tau ∧
      ¬ SameTetVertices sigma rho := by
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
      _hnonself,
      _hsd,
      _hse,
      _hrealized',
      _hthree',
      _hobstruction'⟩

  have htauNodup :
      tau.verts.Nodup :=
    hcore.1 tau htauK

  have hrhoNodup :
      rho.verts.Nodup :=
    hcore.1 rho hrhoK

  have hfive :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct
      s
      hrealized

  have habc :
      [s.a, s.b, s.c].Nodup := by
    simp only [
      List.nodup_cons,
      List.mem_cons,
      List.mem_singleton,
      not_or
    ] at hfive ⊢
    aesop

  obtain
      ⟨d,
        e,
        hdTau,
        hdABC,
        heRho,
        heABC,
        hde,
        hTauCover,
        hRhoCover⟩ :=
    Tet.exists_distinct_complement_vertices
      tau
      rho
      htauNodup
      hrhoNodup
      habc
      haTau
      hbTau
      hcTau
      haRho
      hbRho
      hcRho
      hTauRho

  have hxd :
      x = d := by
    rcases hTauCover x hxTau with
      h | h | h | h
    · exact False.elim (hxABC (by simp [h]))
    · exact False.elim (hxABC (by simp [h]))
    · exact False.elim (hxABC (by simp [h]))
    · exact h

  have hye :
      y = e := by
    rcases hRhoCover y hyRho with
      h | h | h | h
    · exact False.elim (hyABC (by simp [h]))
    · exact False.elim (hyABC (by simp [h]))
    · exact False.elim (hyABC (by simp [h]))
    · exact h

  have hyNotTau :
      y ∉ tau.verts := by
    intro hyTau

    rcases hTauCover y hyTau with
      h | h | h | h

    · exact hyABC (by simp [h])
    · exact hyABC (by simp [h])
    · exact hyABC (by simp [h])
    · exact hxy (hxd.trans h.symm)

  have hxNotRho :
      x ∉ rho.verts := by
    intro hxRho

    rcases hRhoCover x hxRho with
      h | h | h | h

    · exact hxABC (by simp [h])
    · exact hxABC (by simp [h])
    · exact hxABC (by simp [h])
    · exact hxy (h.trans hye.symm)

  have hSigmaTau :
      ¬ SameTetVertices sigma tau := by
    intro hsame

    have hyTau :
        y ∈ tau.verts :=
      (hsame y).1 hySigma

    exact hyNotTau hyTau

  have hSigmaRho :
      ¬ SameTetVertices sigma rho := by
    intro hsame

    have hxRho :
        x ∈ rho.verts :=
      (hsame x).1 hxSigma

    exact hxNotRho hxRho

  exact
    ⟨tau,
      rho,
      x,
      y,
      sigma,
      htauK,
      hrhoK,
      hsigmaK,
      hxTau,
      hyRho,
      hxSigma,
      hySigma,
      hyNotTau,
      hxNotRho,
      hTauRho,
      hSigmaTau,
      hSigmaRho⟩

end Poincare
