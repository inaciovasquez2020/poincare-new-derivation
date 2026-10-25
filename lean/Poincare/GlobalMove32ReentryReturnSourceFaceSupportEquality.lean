import Poincare.GlobalMove32ReentryReturnSourceFaceCarrierEscape
import Poincare.GlobalMove32ReentryReturnTargetStarEquivalence
import Mathlib.Tactic

namespace Poincare

/--
Equal supported-edge states force equality of the unordered source-face
supports. The only alternative supplied by the source-face classifier is
eliminated by transporting a represented return target tetrahedron into the
anchor target star: its escaping source vertex would then belong to the
anchor's five-vertex carrier, a contradiction.

This is a local recurrent-return rigidity lemma. It does not prove literal
site equality, cycle impossibility, termination, or the global Poincare
conclusion.
-/
theorem ClosedTriangulationCore.sourceFace_support_eq_of_sharedSupportedEdgeState_eq
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hanchorThree : anchor.SharedEdgeExactlyThree K)
    (hretRealized : ret.RealizedIn K)
    (hretThree : ret.SharedEdgeExactlyThree K)
    (hstate :
      sharedSupportedEdgeState hcore anchor hanchorRealized =
        sharedSupportedEdgeState hcore ret hretRealized)
    (hreturnEdge :
      (ret.d = anchor.d ∧ ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧ ret.e = anchor.d))
    {sigma : Tet}
    (hsigmaK : sigma ∈ K.tets)
    (hretD : ret.d ∈ sigma.verts)
    (hretE : ret.e ∈ sigma.verts)
    (hanchorTarget :
      SameTetVertices sigma anchor.targetTet₀ ∨
      SameTetVertices sigma anchor.targetTet₁ ∨
      SameTetVertices sigma anchor.targetTet₂) :
    ∀ z : Nat,
      z ∈ [anchor.a, anchor.b, anchor.c] ↔
      z ∈ [ret.a, ret.b, ret.c] := by
  classical
  have hstar :=
    hcore.targetStar_equiv_of_sharedSupportedEdgeState_eq
      anchor ret hanchorRealized hanchorThree hretRealized hretThree hstate
  obtain hsame | hescape :=
    hcore.sourceFace_support_eq_or_distinct_third_vertex_outside_anchor_carrier_of_return_target
      anchor ret hanchorRealized hretRealized hretThree
      hsigmaK hretD hretE hreturnEdge hanchorTarget
  · exact hsame
  · obtain
        ⟨u, v, p, q, huv, hpu, hpv, hqu, hqv,
          hpAnchor, hqRet, hanchorExact, hretExact, hpq, hqOutside⟩ :=
      hescape
    have hqCases : q = ret.a ∨ q = ret.b ∨ q = ret.c := by
      simpa using hqRet
    obtain ⟨⟨tau0, htau0, hsame0⟩,
      ⟨tau1, htau1, hsame1⟩,
      ⟨tau2, htau2, hsame2⟩⟩ := hretRealized
    have hqInAnchorCarrier :
        q ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
      rcases hqCases with hqa | hqb | hqc
      · have hqTau : q ∈ tau0.verts := by
          apply (hsame0 q).mpr
          simp [Move32Site.targetTet₀, Tet.verts, hqa]
        have hanchorStar :
            SameTetVertices tau0 anchor.targetTet₀ ∨
            SameTetVertices tau0 anchor.targetTet₁ ∨
            SameTetVertices tau0 anchor.targetTet₂ :=
          (hstar tau0 htau0).2 (Or.inl hsame0)
        rcases hanchorStar with ha | hb | hc
        · have hqAnchor := (ha q).mp hqTau
          rcases hqAnchor with h | h | h | h <;> simp [h]
        · have hqAnchor := (hb q).mp hqTau
          rcases hqAnchor with h | h | h | h <;> simp [h]
        · have hqAnchor := (hc q).mp hqTau
          rcases hqAnchor with h | h | h | h <;> simp [h]
      · have hqTau : q ∈ tau0.verts := by
          apply (hsame0 q).mpr
          simp [Move32Site.targetTet₀, Tet.verts, hqb]
        have hanchorStar :
            SameTetVertices tau0 anchor.targetTet₀ ∨
            SameTetVertices tau0 anchor.targetTet₁ ∨
            SameTetVertices tau0 anchor.targetTet₂ :=
          (hstar tau0 htau0).2 (Or.inl hsame0)
        rcases hanchorStar with ha | hb | hc
        · have hqAnchor := (ha q).mp hqTau
          rcases hqAnchor with h | h | h | h <;> simp [h]
        · have hqAnchor := (hb q).mp hqTau
          rcases hqAnchor with h | h | h | h <;> simp [h]
        · have hqAnchor := (hc q).mp hqTau
          rcases hqAnchor with h | h | h | h <;> simp [h]
      · have hqTau : q ∈ tau1.verts := by
          apply (hsame1 q).mpr
          simp [Move32Site.targetTet₁, Tet.verts, hqc]
        have hanchorStar :
            SameTetVertices tau1 anchor.targetTet₀ ∨
            SameTetVertices tau1 anchor.targetTet₁ ∨
            SameTetVertices tau1 anchor.targetTet₂ :=
          (hstar tau1 htau1).2 (Or.inr (Or.inl hsame1))
        rcases hanchorStar with ha | hb | hc
        · have hqAnchor := (ha q).mp hqTau
          rcases hqAnchor with h | h | h | h <;> simp [h]
        · have hqAnchor := (hb q).mp hqTau
          rcases hqAnchor with h | h | h | h <;> simp [h]
        · have hqAnchor := (hc q).mp hqTau
          rcases hqAnchor with h | h | h | h <;> simp [h]
    exact (hqOutside hqInAnchorCarrier).elim

end Poincare
