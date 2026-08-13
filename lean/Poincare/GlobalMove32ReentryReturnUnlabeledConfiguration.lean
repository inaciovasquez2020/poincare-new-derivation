import Poincare.GlobalMove32ReentryReturnFiveVertexCarrier
import Poincare.GlobalMove32ReentryReturnTargetStarEquivalence

namespace Poincare

/--
If two realized incidence-three Move32 sites have the same source-face support
and the same supported-edge state, then their complete unlabeled local
configuration agrees in the following precise senses:

* the shared edge has the same unordered endpoints;
* the five-vertex carrier has the same support;
* the represented three-tetrahedron target star is identical up to
  `SameTetVertices`.

This does not assert equality of the ordered `Move32Site` fields and does not
exclude a finite recurrent relabeling cycle.
-/
theorem
    ClosedTriangulationCore.unlabeledConfiguration_eq_of_sourceFace_support_eq_of_sharedSupportedEdgeState_eq
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hanchorThree : anchor.SharedEdgeExactlyThree K)
    (hretRealized : ret.RealizedIn K)
    (hretThree : ret.SharedEdgeExactlyThree K)
    (hsource :
      ∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] ↔
        z ∈ [ret.a, ret.b, ret.c])
    (hstate :
      sharedSupportedEdgeState
          hcore anchor hanchorRealized =
        sharedSupportedEdgeState
          hcore ret hretRealized) :
    (((anchor.d = ret.d ∧ anchor.e = ret.e) ∨
      (anchor.d = ret.e ∧ anchor.e = ret.d)) ∧
     (∀ z : Nat,
       z ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] ↔
       z ∈ [ret.a, ret.b, ret.c, ret.d, ret.e]) ∧
     (∀ tau : Tet,
       tau ∈ K.tets →
         ((SameTetVertices tau anchor.targetTet₀ ∨
           SameTetVertices tau anchor.targetTet₁ ∨
           SameTetVertices tau anchor.targetTet₂) ↔
          (SameTetVertices tau ret.targetTet₀ ∨
           SameTetVertices tau ret.targetTet₁ ∨
           SameTetVertices tau ret.targetTet₂)))) := by
  have hanchorDistinct :
      anchor.d ≠ anchor.e :=
    (hcore.move32_sharedEdge_supported
      anchor hanchorRealized).2.2

  have hretDistinct :
      ret.d ≠ ret.e :=
    (hcore.move32_sharedEdge_supported
      ret hretRealized).2.2

  have hkey :
      canonicalEdgeKey anchor.d anchor.e =
        canonicalEdgeKey ret.d ret.e := by
    calc
      canonicalEdgeKey anchor.d anchor.e =
          (sharedSupportedEdgeState
            hcore anchor hanchorRealized).key :=
        (sharedSupportedEdgeState_key
          hcore anchor hanchorRealized).symm
      _ =
          (sharedSupportedEdgeState
            hcore ret hretRealized).key :=
        congrArg (fun q => q.key) hstate
      _ =
          canonicalEdgeKey ret.d ret.e :=
        sharedSupportedEdgeState_key
          hcore ret hretRealized

  have hedge :
      (anchor.d = ret.d ∧ anchor.e = ret.e) ∨
      (anchor.d = ret.e ∧ anchor.e = ret.d) :=
    (canonicalEdgeKey_eq_iff
      anchor.d
      anchor.e
      ret.d
      ret.e
      hanchorDistinct
      hretDistinct).1 hkey

  have hcarrier :
      ∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] ↔
        z ∈ [ret.a, ret.b, ret.c, ret.d, ret.e] :=
    hcore.fiveVertex_support_eq_of_sourceFace_support_eq_of_sharedSupportedEdgeState_eq
      anchor
      ret
      hanchorRealized
      hretRealized
      hsource
      hstate

  have htarget :
      ∀ tau : Tet,
        tau ∈ K.tets →
          ((SameTetVertices tau anchor.targetTet₀ ∨
            SameTetVertices tau anchor.targetTet₁ ∨
            SameTetVertices tau anchor.targetTet₂) ↔
           (SameTetVertices tau ret.targetTet₀ ∨
            SameTetVertices tau ret.targetTet₁ ∨
            SameTetVertices tau ret.targetTet₂)) :=
    hcore.targetStar_equiv_of_sharedSupportedEdgeState_eq
      anchor
      ret
      hanchorRealized
      hanchorThree
      hretRealized
      hretThree
      hstate

  exact ⟨hedge, hcarrier, htarget⟩

end Poincare
