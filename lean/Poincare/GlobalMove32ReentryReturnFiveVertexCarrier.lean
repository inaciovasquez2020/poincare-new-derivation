import Poincare.GlobalMove32ReentryReturnSourceFaceSameSupport
import Mathlib.Tactic

namespace Poincare

/--
If two realized Move32 sites have the same source-face vertex support and the
same canonical supported-edge state, then they have the same unordered
five-vertex carrier.

This is weaker than equality of `Move32Site`: the source triple may be
permuted and the shared edge may be reversed.  No cycle-impossibility or
termination statement is asserted.
-/
theorem
    ClosedTriangulationCore.fiveVertex_support_eq_of_sourceFace_support_eq_of_sharedSupportedEdgeState_eq
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hretRealized : ret.RealizedIn K)
    (hsource :
      ∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] ↔
        z ∈ [ret.a, ret.b, ret.c])
    (hstate :
      sharedSupportedEdgeState
          hcore anchor hanchorRealized =
        sharedSupportedEdgeState
          hcore ret hretRealized) :
    ∀ z : Nat,
      z ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] ↔
      z ∈ [ret.a, ret.b, ret.c, ret.d, ret.e] := by
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

  have hendpoints :
      (anchor.d = ret.d ∧ anchor.e = ret.e) ∨
      (anchor.d = ret.e ∧ anchor.e = ret.d) :=
    (canonicalEdgeKey_eq_iff
      anchor.d
      anchor.e
      ret.d
      ret.e
      hanchorDistinct
      hretDistinct).1 hkey

  have hedge :
      ∀ z : Nat,
        (z = anchor.d ∨ z = anchor.e) ↔
        (z = ret.d ∨ z = ret.e) := by
    intro z
    rcases hendpoints with hsame | hswap

    · rcases hsame with ⟨hd, he⟩
      rw [hd, he]

    · rcases hswap with ⟨hd, he⟩
      rw [hd, he]
      exact or_comm

  intro z

  have hanchorFive :
      z ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e] ↔
      (z ∈ [anchor.a, anchor.b, anchor.c] ∨
       z = anchor.d ∨
       z = anchor.e) := by
    simp [or_assoc]

  have hretFive :
      z ∈ [ret.a, ret.b, ret.c, ret.d, ret.e] ↔
      (z ∈ [ret.a, ret.b, ret.c] ∨
       z = ret.d ∨
       z = ret.e) := by
    simp [or_assoc]

  rw [
    hanchorFive,
    hretFive,
    hsource z,
    hedge z
  ]

end Poincare
