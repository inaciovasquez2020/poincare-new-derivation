import Poincare.GlobalMove32WitnessedReentryFreshEndpoints
import Mathlib.Tactic

namespace Poincare

/--
Suppose a witnessed reentry returns to the unordered shared edge of an earlier
realized Move32 anchor.  If the predecessor shared-edge endpoint `s.d` is known
to lie in the anchor five-vertex carrier, while the predecessor source face is
not the anchor source face, then the no-degree-four freshness theorem forces
strict carrier escape in two senses:

* `s.d` is one of the anchor source vertices `a,b,c`, never anchor `d,e`;
* the predecessor source face contains a vertex outside the entire anchor
  five-vertex carrier.

This is a local combinatorial consequence only.  It does not claim that the
resulting extra outside vertex is globally fresh along a longer recurrence.
-/
theorem ClosedTriangulationCore.exists_anchorSource_endpoint_and_new_source_vertex_of_witnessedReentry_return_edge
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (anchor s ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hsRealized : s.RealizedIn K)
    (hstep : Move32SourceFaceWitnessedReentry K s ret)
    (hreturn :
      (ret.d = anchor.d ∧ ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧ ret.e = anchor.d))
    (hsDInside :
      s.d ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e])
    (hsourceNe :
      ¬ (∀ z : Nat,
        z ∈ [s.a, s.b, s.c] ↔
        z ∈ [anchor.a, anchor.b, anchor.c])) :
    (s.d = anchor.a ∨ s.d = anchor.b ∨ s.d = anchor.c) ∧
      ∃ q : Nat,
        q ∈ [s.a, s.b, s.c] ∧
        q ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
  classical

  have hfresh :=
    hcore.witnessedReentry_next_sharedEdge_disjoint_previous_carrier_of_no_degree_four
      hlinks hNoFour s ret hsRealized hstep

  rw [List.disjoint_left] at hfresh

  have hanchorDNotCarrier :
      anchor.d ∉ [s.a, s.b, s.c, s.d, s.e] := by
    intro hmem
    apply hfresh anchor.d
    · rcases hreturn with hdirect | hreverse
      · simpa [hdirect.1]
      · simpa [hreverse.2]
    · exact hmem

  have hanchorENotCarrier :
      anchor.e ∉ [s.a, s.b, s.c, s.d, s.e] := by
    intro hmem
    apply hfresh anchor.e
    · rcases hreturn with hdirect | hreverse
      · simpa [hdirect.2]
      · simpa [hreverse.1]
    · exact hmem

  have hsDneD : s.d ≠ anchor.d := by
    intro h
    apply hanchorDNotCarrier
    rw [← h]
    simp

  have hsDneE : s.d ≠ anchor.e := by
    intro h
    apply hanchorENotCarrier
    rw [← h]
    simp

  have hsDClass :
      s.d = anchor.a ∨ s.d = anchor.b ∨ s.d = anchor.c := by
    simp only [List.mem_cons, List.mem_singleton] at hsDInside
    aesop

  have hsourceOutside :
      ∃ q : Nat,
        q ∈ [s.a, s.b, s.c] ∧
        q ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
    by_contra hnone

    have hsourceInsideFive :
        ∀ q : Nat,
          q ∈ [s.a, s.b, s.c] →
          q ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
      intro q hq
      by_contra hqOut
      exact hnone ⟨q, hq, hqOut⟩

    have hsourceSubset :
        ∀ q : Nat,
          q ∈ [s.a, s.b, s.c] →
          q ∈ [anchor.a, anchor.b, anchor.c] := by
      intro q hq

      have hqFive := hsourceInsideFive q hq

      have hqCarrier : q ∈ [s.a, s.b, s.c, s.d, s.e] := by
        simp only [List.mem_cons, List.mem_singleton] at hq ⊢
        aesop

      have hqNeD : q ≠ anchor.d := by
        intro h
        apply hanchorDNotCarrier
        rw [← h]
        exact hqCarrier

      have hqNeE : q ≠ anchor.e := by
        intro h
        apply hanchorENotCarrier
        rw [← h]
        exact hqCarrier

      simp only [List.mem_cons, List.mem_singleton] at hqFive ⊢
      aesop

    have hsNodup : [s.a, s.b, s.c].Nodup := by
      have h := hcore.move32Site_distinct s hsRealized
      simp at h ⊢
      aesop

    have hanchorNodup : [anchor.a, anchor.b, anchor.c].Nodup := by
      have h := hcore.move32Site_distinct anchor hanchorRealized
      simp at h ⊢
      aesop

    let S : Finset Nat := [s.a, s.b, s.c].toFinset
    let A : Finset Nat := [anchor.a, anchor.b, anchor.c].toFinset

    have hsub : S ⊆ A := by
      intro q hq
      apply List.mem_toFinset.mpr
      apply hsourceSubset q
      exact List.mem_toFinset.mp hq

    have hScard : S.card = 3 := by
      dsimp [S]
      rw [List.toFinset_card_of_nodup hsNodup]
      simp

    have hAcard : A.card = 3 := by
      dsimp [A]
      rw [List.toFinset_card_of_nodup hanchorNodup]
      simp

    have hEq : S = A :=
      Finset.eq_of_subset_of_card_le hsub (by omega)

    have hsourceEq :
        ∀ z : Nat,
          z ∈ [s.a, s.b, s.c] ↔
          z ∈ [anchor.a, anchor.b, anchor.c] := by
      intro z
      constructor
      · intro hz
        have hzS : z ∈ S := List.mem_toFinset.mpr hz
        rw [hEq] at hzS
        exact List.mem_toFinset.mp hzS
      · intro hz
        have hzA : z ∈ A := List.mem_toFinset.mpr hz
        rw [← hEq] at hzA
        exact List.mem_toFinset.mp hzA

    exact hsourceNe hsourceEq

  exact ⟨hsDClass, hsourceOutside⟩

end Poincare
