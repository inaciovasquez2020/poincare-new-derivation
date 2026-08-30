import Poincare.GlobalMove32ReentryFirstNonzeroExhaustiveFork
import Poincare.GlobalMove32IncidenceThreeCandidate

namespace Poincare

/-- The exact-incidence-three half of the one-sided refined-ear cross-edge
branch already feeds the repository's generic incidence-three candidate
constructor.  Thus it produces a realized Move32 site with exact-three shared
edge on that cross edge.  This deliberately does not assert `SourceFaceAbsent`
or `LegalIn`. -/
theorem ClosedTriangulationCore.exists_move32Site_realizedIn_of_firstEar_crossEdge_incidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (v x : Nat)
    (hcross :
      (v = anchor.b ∧ x = anchor.d) ∨
        (v = anchor.b ∧ x = anchor.e) ∨
        (v = anchor.a ∧ x = anchor.d) ∨
        (v = anchor.a ∧ x = anchor.e))
    (hthree :
      (K.tets.filter
        (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length = 3) :
    ∃ s : Move32Site,
      s.d = v ∧
      s.e = x ∧
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K := by
  have hdistinct := hcore.move32Site_distinct anchor hanchorRealized

  have hbD : anchor.b ≠ anchor.d := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have hbE : anchor.b ≠ anchor.e := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have haD : anchor.a ≠ anchor.d := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have haE : anchor.a ≠ anchor.e := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have hvx : v ≠ x := by
    rcases hcross with hbd | hbe | had | hae
    · simpa [hbd.1, hbd.2] using hbD
    · simpa [hbe.1, hbe.2] using hbE
    · simpa [had.1, had.2] using haD
    · simpa [hae.1, hae.2] using haE

  exact hcore.exists_move32Site_realizedIn_of_edgeIncidence_three
    v x hvx hthree

end Poincare
