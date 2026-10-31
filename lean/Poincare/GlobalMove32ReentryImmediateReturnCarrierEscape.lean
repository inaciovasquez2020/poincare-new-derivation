import Poincare.GlobalMove32WitnessedReentryFreshEndpoints
import Mathlib.Tactic
import Poincare.GlobalEdgeCyclicFan

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

/-- A shortest possible nonconsecutive witnessed-reentry shared-edge return
(anchor -> mid -> ret) forces each intermediate shared edge to lie outside
the other's entire five-vertex carrier. This is a necessary geometric
constraint, not acyclicity or a global Poincare claim. -/
theorem ClosedTriangulationCore.witnessedReentry_two_step_return_cross_disjoint
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (anchor mid ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hmidRealized : mid.RealizedIn K)
    (hstep0 : Move32SourceFaceWitnessedReentry K anchor mid)
    (hstep1 : Move32SourceFaceWitnessedReentry K mid ret)
    (hreturn :
      (ret.d = anchor.d ∧ ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧ ret.e = anchor.d)) :
    List.Disjoint [mid.d, mid.e]
      [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] ∧
    List.Disjoint [anchor.d, anchor.e]
      [mid.a, mid.b, mid.c, mid.d, mid.e] := by
  constructor
  · exact
      hcore.witnessedReentry_next_sharedEdge_disjoint_previous_carrier_of_no_degree_four
        hlinks hNoFour anchor mid hanchorRealized hstep0
  · have hfresh :=
      hcore.witnessedReentry_next_sharedEdge_disjoint_previous_carrier_of_no_degree_four
        hlinks hNoFour mid ret hmidRealized hstep1
    rw [List.disjoint_left] at hfresh ⊢
    intro z hzAnchor hzMid
    have hzRet : z ∈ [ret.d, ret.e] := by
      rcases hreturn with ⟨hd, he⟩ | ⟨hd, he⟩
      · simpa only [hd, he] using hzAnchor
      · have hz : z = anchor.d ∨ z = anchor.e := by
          simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] using hzAnchor
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false]
        rcases hz with h | h
        · exact Or.inr (h.trans he.symm)
        · exact Or.inl (h.trans hd.symm)
    exact hfresh z hzRet hzMid

/-- The two tetrahedra retained by a witnessed source-face reentry can be
selected in any covering ambient fan about a source-face edge. They are
adjacent at the third source vertex, and their explicit 2-3 candidate uses
the already represented returned edge as its prospective new chord.
No legal 2-3 move or strict descent is asserted. -/
theorem ClosedTriangulationCore.witnessedReentry_representedChord_on_aligned_sourceFace
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s t : Move32Site)
    (hs : s.RealizedIn K)
    (hstep : Move32SourceFaceWitnessedReentry K s t)
    (F : AmbientEdgeCyclicFan K s.a s.b) :
    ∃ α β : {q : LinkTriangle //
        q ∈ vertexLinkStarTriangles K s.a s.b},
      (vertexLinkStarGraph K s.a s.b).Adj α β ∧
      ∃ m : Move23Site,
        m.a = s.a ∧ m.b = s.b ∧ m.c = s.c ∧
        m.d = t.d ∧ m.e = t.e ∧
        SameTetVertices (F.tetAt α) m.leftTet ∧
        SameTetVertices (F.tetAt β) m.rightTet ∧
        ¬ m.NewEdgeAbsent K := by
  classical
  rcases hstep with
    ⟨tau, rho, x, y, sigma,
      htauK, hrhoK, hTauRho,
      haTau, hbTau, hcTau,
      haRho, hbRho, hcRho,
      hxTau, hxABC, hyRho, hyABC, hxy,
      hsigmaK, hxSigma, hySigma, _hnonself,
      htd, hte, _htRealized, _htThree, _htObstruction⟩
  subst x
  subst y
  have habc : [s.a, s.b, s.c].Nodup := by
    have hfive := hcore.move32Site_distinct s hs
    simp at hfive ⊢
    aesop
  have hca : s.c ≠ s.a := by
    have hfive := hcore.move32Site_distinct s hs
    simp at hfive
    aesop
  have hcb : s.c ≠ s.b := by
    have hfive := hcore.move32Site_distinct s hs
    simp at hfive
    aesop
  obtain ⟨α, hα⟩ := F.covers_ambient tau htauK haTau hbTau
  obtain ⟨β, hβ⟩ := F.covers_ambient rho hrhoK haRho hbRho
  have hαβ : α ≠ β := by
    intro heq
    apply hTauRho
    have hTet : tau = rho := by
      calc
        tau = F.tetAt α := hα.symm
        _ = F.tetAt β := by rw [heq]
        _ = rho := hβ
    rw [hTet]
    exact sameTetVertices_refl rho
  have hlinkα : tau.linkTriangleAt? s.a = some α.1 := by
    simpa only [hα] using F.tetAt_link α
  have hlinkβ : rho.linkTriangleAt? s.a = some β.1 := by
    simpa only [hβ] using F.tetAt_link β
  have hcα : s.c ∈ α.1.verts :=
    (tau.mem_linkTriangleAt?_iff s.a s.c α.1 hlinkα hca).2 hcTau
  have hcβ : s.c ∈ β.1.verts :=
    (rho.mem_linkTriangleAt?_iff s.a s.c β.1 hlinkβ hca).2 hcRho
  have hadj : (vertexLinkStarGraph K s.a s.b).Adj α β :=
    (vertexLinkStarGraph_adj K s.a s.b α β).2
      ⟨hαβ, α.2, β.2, s.c, hcb, hcα, hcβ⟩
  obtain ⟨u, v, _hu, _huABC, _hv, _hvABC, _huv,
      hTauCover, hRhoCover⟩ :=
    Tet.exists_distinct_complement_vertices tau rho
      (hcore.1 tau htauK) (hcore.1 rho hrhoK)
      habc haTau hbTau hcTau haRho hbRho hcRho hTauRho
  have huEq : u = t.d := by
    rcases hTauCover t.d hxTau with h | h | h | h
    · exact (hxABC (by simp [h])).elim
    · exact (hxABC (by simp [h])).elim
    · exact (hxABC (by simp [h])).elim
    · exact h.symm
  have hvEq : v = t.e := by
    rcases hRhoCover t.e hyRho with h | h | h | h
    · exact (hyABC (by simp [h])).elim
    · exact (hyABC (by simp [h])).elim
    · exact (hyABC (by simp [h])).elim
    · exact h.symm
  have hDistinct : [s.a, s.b, s.c, t.d, t.e].Nodup := by
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false] at habc hxABC hyABC ⊢
    aesop
  let m : Move23Site :=
    { a := s.a, b := s.b, c := s.c,
      d := t.d, e := t.e, distinct := hDistinct }
  have hTauSame : SameTetVertices tau m.leftTet := by
    intro z
    constructor
    · intro hz
      rcases hTauCover z hz with h | h | h | h
      · simp [m, Move23Site.leftTet, Tet.verts, h]
      · simp [m, Move23Site.leftTet, Tet.verts, h]
      · simp [m, Move23Site.leftTet, Tet.verts, h]
      · simp [m, Move23Site.leftTet, Tet.verts, h, huEq]
    · intro hz
      simp [m, Move23Site.leftTet, Tet.verts] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact haTau
      · exact hbTau
      · exact hcTau
      · exact hxTau
  have hRhoSame : SameTetVertices rho m.rightTet := by
    intro z
    constructor
    · intro hz
      rcases hRhoCover z hz with h | h | h | h
      · simp [m, Move23Site.rightTet, Tet.verts, h]
      · simp [m, Move23Site.rightTet, Tet.verts, h]
      · simp [m, Move23Site.rightTet, Tet.verts, h]
      · simp [m, Move23Site.rightTet, Tet.verts, h, hvEq]
    · intro hz
      simp [m, Move23Site.rightTet, Tet.verts] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact haRho
      · exact hbRho
      · exact hcRho
      · exact hyRho
  refine ⟨α, β, hadj, m, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa only [hα] using hTauSame
  · simpa only [hβ] using hRhoSame
  · intro habsent
    exact (habsent sigma hsigmaK)
      ⟨by simpa [m] using hxSigma, by simpa [m] using hySigma⟩

end Poincare
