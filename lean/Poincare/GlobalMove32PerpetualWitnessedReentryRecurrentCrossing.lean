import Poincare.GlobalMove32WitnessedFiniteRecurrenceReturn
import Poincare.GlobalMove32ReentryReturnCrossingConfiguration
import Poincare.GlobalMove32WitnessedReentryPerpetualNoMove23
import Poincare.GlobalMove32ReentryReturnSourceFaceCarrierEscape
import Mathlib.Tactic

namespace Poincare

/--
A perpetual sequence of witnessed incidence-three Move32 source-face
reentries has a finite nonconsecutive return whose repeated supported-edge
state carries the full same-witness crossing geometry at the return step.

This is a finite recurrent configuration theorem only.  It does not assert
that such a recurrent configuration is impossible and does not prove
termination.
-/
theorem
    ClosedTriangulationCore.exists_finite_recurrent_return_crossing_configuration_of_perpetual_witnessedReentry
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (sites : ℕ → Move32Site)
    (hrealized : ∀ n, (sites n).RealizedIn K)
    (hthree : ∀ n, (sites n).SharedEdgeExactlyThree K)
    (hwitnessed :
      ∀ n,
        Move32SourceFaceWitnessedReentry
          K (sites n) (sites (n + 1))) :
    ∃ i k tau rho sigma,
      i + 1 < k + 1 ∧
      k + 1 ≤ Fintype.card (SupportedEdgeState K) ∧
      tau ∈ K.tets ∧
      rho ∈ K.tets ∧
      sigma ∈ K.tets ∧
      ¬ SameTetVertices tau rho ∧
      (sites k).a ∈ tau.verts ∧
      (sites k).b ∈ tau.verts ∧
      (sites k).c ∈ tau.verts ∧
      (sites k).a ∈ rho.verts ∧
      (sites k).b ∈ rho.verts ∧
      (sites k).c ∈ rho.verts ∧
      (sites (k + 1)).d ∈ tau.verts ∧
      (sites (k + 1)).e ∈ rho.verts ∧
      (sites (k + 1)).d ∈ sigma.verts ∧
      (sites (k + 1)).e ∈ sigma.verts ∧
      (sites (k + 1)).e ∉ tau.verts ∧
      (sites (k + 1)).d ∉ rho.verts ∧
      ¬ SameTetVertices sigma tau ∧
      ¬ SameTetVertices sigma rho ∧
      (((sites (k + 1)).d = (sites i).d ∧
          (sites (k + 1)).e = (sites i).e) ∨
       ((sites (k + 1)).d = (sites i).e ∧
          (sites (k + 1)).e = (sites i).d)) ∧
      (SameTetVertices sigma (sites i).targetTet₀ ∨
       SameTetVertices sigma (sites i).targetTet₁ ∨
       SameTetVertices sigma (sites i).targetTet₂) := by
  obtain ⟨i, k, hgap, hbound, hstate, hstep, _hreturn⟩ :=
    hcore.exists_recurrent_returnSigma_target_of_perpetual_witnessedReentry
      sites hrealized hthree hwitnessed

  obtain ⟨tau, rho, sigma, hconfig⟩ :=
    hcore.exists_witnessedReentry_return_crossing_anchor_target_of_sharedSupportedEdgeState_eq
      (sites i)
      (sites k)
      (sites (k + 1))
      (hrealized i)
      (hthree i)
      (hrealized k)
      (hrealized (k + 1))
      hstep
      hstate

  exact ⟨i, k, tau, rho, sigma, hgap, hbound, hconfig⟩

/--
If strict topological `PhiSupport` descent and nonself complementary
high-incidence escape are excluded, then the perpetual witnessed-reentry
builder and finite recurrence theorem compose to produce a finite recurrent
return crossing configuration.

The two excluded exit families remain hypotheses; this theorem does not
eliminate the resulting recurrent configuration.
-/
theorem
    ClosedTriangulationCore.exists_finite_recurrent_return_crossing_configuration_of_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ x y sigma,
          x ≠ y ∧
          sigma ∈ K.tets ∧
          x ∈ sigma.verts ∧
          y ∈ sigma.verts ∧
          ¬ ((x = s.d ∧ y = s.e) ∨
             (x = s.e ∧ y = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (x ∈ gamma.verts ∧
                   y ∈ gamma.verts))).length)
    (start : Move32Site)
    (hstartRealized : start.RealizedIn K)
    (hstartThree : start.SharedEdgeExactlyThree K)
    (hstartObstruction :
      ∃ tau ∈ K.tets,
        start.a ∈ tau.verts ∧
        start.b ∈ tau.verts ∧
        start.c ∈ tau.verts) :
    ∃ sites : Nat → Move32Site,
      sites 0 = start ∧
      ∃ i k tau rho sigma,
        i + 1 < k + 1 ∧
        k + 1 ≤ Fintype.card (SupportedEdgeState K) ∧
        tau ∈ K.tets ∧
        rho ∈ K.tets ∧
        sigma ∈ K.tets ∧
        ¬ SameTetVertices tau rho ∧
        (sites k).a ∈ tau.verts ∧
        (sites k).b ∈ tau.verts ∧
        (sites k).c ∈ tau.verts ∧
        (sites k).a ∈ rho.verts ∧
        (sites k).b ∈ rho.verts ∧
        (sites k).c ∈ rho.verts ∧
        (sites (k + 1)).d ∈ tau.verts ∧
        (sites (k + 1)).e ∈ rho.verts ∧
        (sites (k + 1)).d ∈ sigma.verts ∧
        (sites (k + 1)).e ∈ sigma.verts ∧
        (sites (k + 1)).e ∉ tau.verts ∧
        (sites (k + 1)).d ∉ rho.verts ∧
        ¬ SameTetVertices sigma tau ∧
        ¬ SameTetVertices sigma rho ∧
        (((sites (k + 1)).d = (sites i).d ∧
            (sites (k + 1)).e = (sites i).e) ∨
         ((sites (k + 1)).d = (sites i).e ∧
            (sites (k + 1)).e = (sites i).d)) ∧
        (SameTetVertices sigma (sites i).targetTet₀ ∨
         SameTetVertices sigma (sites i).targetTet₁ ∨
         SameTetVertices sigma (sites i).targetTet₂) := by
  obtain ⟨sites, hzero, hrealized, hthree, _hobstruction, hwitnessed⟩ :=
    hcore.exists_perpetual_witnessedReentry_of_noDescent_noHigh
      hlinks hconn hNoFour hNoDescent hNoHigh
      start hstartRealized hstartThree hstartObstruction

  obtain ⟨i, k, tau, rho, sigma, hconfig⟩ :=
    hcore.exists_finite_recurrent_return_crossing_configuration_of_perpetual_witnessedReentry
      sites hrealized hthree hwitnessed

  exact ⟨sites, hzero, i, k, tau, rho, sigma, hconfig⟩

end Poincare


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

  exact
    hcore.sourceFace_support_eq_or_distinct_third_vertex_outside_anchor_carrier_of_return_target
      anchor ret hanchorRealized hretRealized hretThree
      hsigmaK hdSigma heSigma hreturnEdge hanchorTarget

end Poincare
