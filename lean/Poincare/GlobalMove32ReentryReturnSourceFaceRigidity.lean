import Poincare.GlobalMove32ReentryReturnTargetStarEquivalence
import Mathlib.Tactic

namespace Poincare

/--
For realized exact-incidence-three Move32 sites, the canonical unordered
shared-edge state already determines the unordered source-face support.

Indeed, equality of the shared-edge state identifies the represented
three-tetrahedron target stars.  Every anchor source vertex occurs in one of
those target tetrahedra and is distinct from the returned shared-edge
endpoints, hence must be a returned source vertex.  Since both source faces
have exactly three distinct vertices, the supports agree.
-/
theorem
    ClosedTriangulationCore.sourceFace_support_eq_of_sharedSupportedEdgeState_eq
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hanchorThree : anchor.SharedEdgeExactlyThree K)
    (hretRealized : ret.RealizedIn K)
    (hretThree : ret.SharedEdgeExactlyThree K)
    (hstate :
      sharedSupportedEdgeState hcore anchor hanchorRealized =
        sharedSupportedEdgeState hcore ret hretRealized) :
    ∀ z : Nat,
      z ∈ [anchor.a, anchor.b, anchor.c] ↔
        z ∈ [ret.a, ret.b, ret.c] := by
  classical

  have htarget :=
    hcore.targetStar_equiv_of_sharedSupportedEdgeState_eq
      anchor ret hanchorRealized hanchorThree hretRealized hretThree hstate

  have hanchorDistinct : anchor.d ≠ anchor.e :=
    (hcore.move32_sharedEdge_supported anchor hanchorRealized).2.2

  have hretDistinct : ret.d ≠ ret.e :=
    (hcore.move32_sharedEdge_supported ret hretRealized).2.2

  have hkey :
      canonicalEdgeKey anchor.d anchor.e =
        canonicalEdgeKey ret.d ret.e := by
    calc
      canonicalEdgeKey anchor.d anchor.e =
          (sharedSupportedEdgeState hcore anchor hanchorRealized).key :=
        (sharedSupportedEdgeState_key hcore anchor hanchorRealized).symm
      _ = (sharedSupportedEdgeState hcore ret hretRealized).key :=
        congrArg (fun q : SupportedEdgeState K => q.key) hstate
      _ = canonicalEdgeKey ret.d ret.e :=
        sharedSupportedEdgeState_key hcore ret hretRealized

  have hedge :
      (anchor.d = ret.d ∧ anchor.e = ret.e) ∨
      (anchor.d = ret.e ∧ anchor.e = ret.d) :=
    (canonicalEdgeKey_eq_iff
      anchor.d anchor.e ret.d ret.e hanchorDistinct hretDistinct).1 hkey

  have hanchorFive :
      [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e].Nodup :=
    hcore.move32Site_distinct anchor hanchorRealized

  have hretFive :
      [ret.a, ret.b, ret.c, ret.d, ret.e].Nodup :=
    hcore.move32Site_distinct ret hretRealized

  have hanchorSourceNodup : [anchor.a, anchor.b, anchor.c].Nodup := by
    have h := hanchorFive
    simp at h ⊢
    aesop

  have hretSourceNodup : [ret.a, ret.b, ret.c].Nodup := by
    have h := hretFive
    simp at h ⊢
    aesop

  have hsource_ne_anchor_edges
      {z : Nat}
      (hz : z ∈ [anchor.a, anchor.b, anchor.c]) :
      z ≠ anchor.d ∧ z ≠ anchor.e := by
    have h := hanchorFive
    simp only [List.mem_cons, List.mem_singleton] at hz
    simp at h
    rcases hz with rfl | rfl | rfl <;> aesop

  have hsource_ne_ret_edges
      {z : Nat}
      (hz : z ∈ [anchor.a, anchor.b, anchor.c]) :
      z ≠ ret.d ∧ z ≠ ret.e := by
    have hzOld := hsource_ne_anchor_edges hz
    rcases hedge with hdirect | hreverse
    · constructor
      · intro h
        exact hzOld.1 (h.trans hdirect.1.symm)
      · intro h
        exact hzOld.2 (h.trans hdirect.2.symm)
    · constructor
      · intro h
        exact hzOld.2 (h.trans hreverse.2.symm)
      · intro h
        exact hzOld.1 (h.trans hreverse.1.symm)

  have hretSource_of_target
      {tau : Tet} {z : Nat}
      (htau :
        SameTetVertices tau ret.targetTet₀ ∨
        SameTetVertices tau ret.targetTet₁ ∨
        SameTetVertices tau ret.targetTet₂)
      (hzTau : z ∈ tau.verts)
      (hzd : z ≠ ret.d)
      (hze : z ≠ ret.e) :
      z ∈ [ret.a, ret.b, ret.c] := by
    rcases htau with h0 | h1 | h2
    · have hz := (h0 z).1 hzTau
      simp only [Move32Site.targetTet₀, Tet.verts,
        List.mem_cons, List.mem_singleton] at hz ⊢
      aesop
    · have hz := (h1 z).1 hzTau
      simp only [Move32Site.targetTet₁, Tet.verts,
        List.mem_cons, List.mem_singleton] at hz ⊢
      aesop
    · have hz := (h2 z).1 hzTau
      simp only [Move32Site.targetTet₂, Tet.verts,
        List.mem_cons, List.mem_singleton] at hz ⊢
      aesop

  obtain ⟨t0, ht0K, ht0⟩ := hanchorRealized.1
  obtain ⟨t1, ht1K, ht1⟩ := hanchorRealized.2.1

  have hsubset :
      ∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] →
          z ∈ [ret.a, ret.b, ret.c] := by
    intro z hz
    have hzne := hsource_ne_ret_edges hz
    simp only [List.mem_cons, List.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · have hzT : anchor.a ∈ t0.verts :=
        (ht0 anchor.a).2 (by simp [Move32Site.targetTet₀, Tet.verts])
      have hretTarget := (htarget t0 ht0K).1 (Or.inl ht0)
      exact hretSource_of_target hretTarget hzT hzne.1 hzne.2
    · have hzT : anchor.b ∈ t0.verts :=
        (ht0 anchor.b).2 (by simp [Move32Site.targetTet₀, Tet.verts])
      have hretTarget := (htarget t0 ht0K).1 (Or.inl ht0)
      exact hretSource_of_target hretTarget hzT hzne.1 hzne.2
    · have hzT : anchor.c ∈ t1.verts :=
        (ht1 anchor.c).2 (by simp [Move32Site.targetTet₁, Tet.verts])
      have hretTarget := (htarget t1 ht1K).1 (Or.inr (Or.inl ht1))
      exact hretSource_of_target hretTarget hzT hzne.1 hzne.2

  let A : Finset Nat := [anchor.a, anchor.b, anchor.c].toFinset
  let R : Finset Nat := [ret.a, ret.b, ret.c].toFinset

  have hAR : A ⊆ R := by
    intro z hz
    apply List.mem_toFinset.mpr
    apply hsubset z
    exact List.mem_toFinset.mp hz

  have hAcard : A.card = 3 := by
    dsimp [A]
    rw [List.toFinset_card_of_nodup hanchorSourceNodup]
    simp

  have hRcard : R.card = 3 := by
    dsimp [R]
    rw [List.toFinset_card_of_nodup hretSourceNodup]
    simp

  have hEq : A = R :=
    Finset.eq_of_subset_of_card_le hAR (by omega)

  intro z
  constructor
  · intro hz
    exact hsubset z hz
  · intro hz
    have hzR : z ∈ R := List.mem_toFinset.mpr hz
    rw [← hEq] at hzR
    exact List.mem_toFinset.mp hzR

end Poincare
