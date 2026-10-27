import Poincare.GlobalMove32PerpetualWitnessedReentryRecurrentCrossing
import Poincare.GlobalMove32ReentryReturnSourceFaceCarrierEscape
import Mathlib.Tactic

namespace Poincare

/--
The recurrent witnessed-return crossing configuration has a sharper
source-face dichotomy: either the anchor and return source faces have the same
unordered support, or the returned source face introduces a vertex outside
the anchor's five-vertex carrier.

This packages the existing return-target and carrier-escape lemmas at the
exact repeated-state boundary. It is a geometric dichotomy, not a cycle
contradiction.
-/
theorem
    ClosedTriangulationCore.recurrent_return_sourceFace_support_eq_or_escape_of_witnessedReentry
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor prev ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hanchorThree : anchor.SharedEdgeExactlyThree K)
    (hprevRealized : prev.RealizedIn K)
    (hretRealized : ret.RealizedIn K)
    (hretThree : ret.SharedEdgeExactlyThree K)
    (hstep : Move32SourceFaceWitnessedReentry K prev ret)
    (hstate :
      sharedSupportedEdgeState hcore anchor hanchorRealized =
        sharedSupportedEdgeState hcore ret hretRealized) :
    (∀ z : Nat,
      z ∈ [anchor.a, anchor.b, anchor.c] ↔
        z ∈ [ret.a, ret.b, ret.c]) ∨
    ∃ u v p q,
      u ≠ v ∧
      p ≠ u ∧ p ≠ v ∧
      q ≠ u ∧ q ≠ v ∧
      p ∈ [anchor.a, anchor.b, anchor.c] ∧
      q ∈ [ret.a, ret.b, ret.c] ∧
      (∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] ↔
          z = u ∨ z = v ∨ z = p) ∧
      (∀ z : Nat,
        z ∈ [ret.a, ret.b, ret.c] ↔
          z = u ∨ z = v ∨ z = q) ∧
      p ≠ q ∧
      q ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] := by
  have htarget :=
    hcore.exists_returnSigma_same_anchor_target_of_witnessedReentry_of_sharedSupportedEdgeState_eq
      anchor prev ret hanchorRealized hanchorThree hretRealized
      hstep hstate.symm

  rcases htarget with ⟨sigma, hsigmaK, hdSigma, heSigma, hanchorTarget⟩

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

  have hreturnEdge :
      (ret.d = anchor.d ∧ ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧ ret.e = anchor.d) :=
    (canonicalEdgeKey_eq_iff ret.d ret.e anchor.d anchor.e
      hretDistinct hanchorDistinct).1 hkey.symm

  have hretDSigma : ret.d ∈ sigma.verts := by
    rcases hreturnEdge with hdirect | hreverse
    · rw [hdirect.1]
      exact hdSigma
    · rw [hreverse.1]
      exact heSigma

  have hretESigma : ret.e ∈ sigma.verts := by
    rcases hreturnEdge with hdirect | hreverse
    · rw [hdirect.2]
      exact heSigma
    · rw [hreverse.2]
      exact hdSigma

  exact
    hcore.sourceFace_support_eq_or_distinct_third_vertex_outside_anchor_carrier_of_return_target
      anchor ret hanchorRealized hretRealized hretThree
      hsigmaK hretDSigma hretESigma hreturnEdge hanchorTarget

end Poincare
