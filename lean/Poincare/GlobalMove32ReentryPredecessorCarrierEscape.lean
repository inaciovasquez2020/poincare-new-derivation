import Poincare.GlobalMove32ReentryPredecessorSourceFaceObstruction
import Mathlib.Tactic

namespace Poincare

/--
In the no-degree-four branch, if a witnessed source-face reentry returns to
the shared edge of an earlier anchor Move32 site, then the predecessor source
face cannot merely rotate inside the anchor's five-vertex Move32 carrier.

At least one predecessor source-face vertex lies outside the entire anchor
carrier `[a,b,c,d,e]`.

This strengthens predecessor-source-face inequality to an actual carrier
escape.  No acyclicity or termination conclusion is asserted here.
-/
theorem
    ClosedTriangulationCore.exists_predecessor_sourceFace_vertex_outside_anchor_carrier_of_witnessedReentry_return_edge_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn :
      TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (anchor prev ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hprevRealized : prev.RealizedIn K)
    (hstep :
      Move32SourceFaceWitnessedReentry
        K prev ret)
    (hreturn :
      (ret.d = anchor.d ∧ ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧ ret.e = anchor.d)) :
    ∃ z : Nat,
      z ∈ [prev.a, prev.b, prev.c] ∧
      z ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by

  have hsourceNe :
      ¬ (∀ z : Nat,
        z ∈ [prev.a, prev.b, prev.c] ↔
        z ∈ [anchor.a, anchor.b, anchor.c]) :=
    hcore.not_predecessor_sourceFace_support_eq_anchor_of_witnessedReentry_return_edge_of_no_degree_four
      hlinks
      hconn
      hNoFour
      anchor
      prev
      ret
      hanchorRealized
      hstep
      hreturn

  rcases hstep with
    ⟨tau, rho, x, y, sigma,
      htauK,
      hrhoK,
      hne,
      hprevATau,
      hprevBTau,
      hprevCTau,
      hprevARho,
      hprevBRho,
      hprevCRho,
      hxTau,
      hxPrevABC,
      hyRho,
      hyPrevABC,
      hxy,
      hsigmaK,
      hxSigma,
      hySigma,
      hnonself,
      hretD,
      hretE,
      hretRealized,
      hretThree,
      hgamma⟩

  have hanchorDNotPrev :
      anchor.d ∉ [prev.a, prev.b, prev.c] := by
    intro hz
    have hret := hreturn
    rcases hret with hdirect | hreverse
    · have hxD :
          x = anchor.d :=
        hretD.symm.trans hdirect.1
      exact
        hxPrevABC
          (by simpa [hxD] using hz)
    · have hyD :
          y = anchor.d :=
        hretE.symm.trans hreverse.2
      exact
        hyPrevABC
          (by simpa [hyD] using hz)

  have hanchorENotPrev :
      anchor.e ∉ [prev.a, prev.b, prev.c] := by
    intro hz
    have hret := hreturn
    rcases hret with hdirect | hreverse
    · have hyE :
          y = anchor.e :=
        hretE.symm.trans hdirect.2
      exact
        hyPrevABC
          (by simpa [hyE] using hz)
    · have hxE :
          x = anchor.e :=
        hretD.symm.trans hreverse.1
      exact
        hxPrevABC
          (by simpa [hxE] using hz)

  by_contra houtside
  push_neg at houtside

  have hsubset :
      ∀ z : Nat,
        z ∈ [prev.a, prev.b, prev.c] →
        z ∈ [anchor.a, anchor.b, anchor.c] := by
    intro z hzPrev
    have hzCarrier := houtside z hzPrev
    simp at hzCarrier ⊢
    rcases hzCarrier with hza | hzb | hzc | hzd | hze
    · exact Or.inl hza
    · exact Or.inr (Or.inl hzb)
    · exact Or.inr (Or.inr hzc)
    · exfalso
      apply hanchorDNotPrev
      simpa [hzd] using hzPrev
    · exfalso
      apply hanchorENotPrev
      simpa [hze] using hzPrev

  have hpa :
      prev.a ∈ [anchor.a, anchor.b, anchor.c] :=
    hsubset prev.a (by simp)

  have hpb :
      prev.b ∈ [anchor.a, anchor.b, anchor.c] :=
    hsubset prev.b (by simp)

  have hpc :
      prev.c ∈ [anchor.a, anchor.b, anchor.c] :=
    hsubset prev.c (by simp)

  have hprevFive :
      [prev.a, prev.b, prev.c, prev.d, prev.e].Nodup :=
    hcore.move32Site_distinct prev hprevRealized

  have hanchorFive :
      [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e].Nodup :=
    hcore.move32Site_distinct anchor hanchorRealized

  have hsourceEq :
      ∀ z : Nat,
        z ∈ [prev.a, prev.b, prev.c] ↔
        z ∈ [anchor.a, anchor.b, anchor.c] := by
    intro z
    constructor
    · exact hsubset z
    · intro hzAnchor
      have hprevANotTail :
          prev.a ∉ [prev.b, prev.c, prev.d, prev.e] :=
        (List.nodup_cons.mp hprevFive).1

      have hprevTailNodup :
          [prev.b, prev.c, prev.d, prev.e].Nodup :=
        (List.nodup_cons.mp hprevFive).2

      have hprevBNotTail :
          prev.b ∉ [prev.c, prev.d, prev.e] :=
        (List.nodup_cons.mp hprevTailNodup).1

      have hprevAB :
          prev.a ≠ prev.b := by
        intro hab
        apply hprevANotTail
        simp [hab]

      have hprevAC :
          prev.a ≠ prev.c := by
        intro hac
        apply hprevANotTail
        simp [hac]

      have hprevBC :
          prev.b ≠ prev.c := by
        intro hbc
        apply hprevBNotTail
        simp [hbc]

      simp at hpa hpb hpc hzAnchor ⊢
      rcases hzAnchor with hza | hzb | hzc
      · omega
      · omega
      · omega

  exact hsourceNe hsourceEq

end Poincare
