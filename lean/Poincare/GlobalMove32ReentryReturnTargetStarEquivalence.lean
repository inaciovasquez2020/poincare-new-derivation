import Poincare.GlobalMove32ReentryReturnFiveVertexCarrier
import Mathlib.Tactic

namespace Poincare

/--
Two realized incidence-three Move32 sites with the same supported shared-edge
state have the same represented three-tetrahedron target star, independently
of source-face label permutations and independently of the orientation of the
shared edge.

This is an unlabeled target-star equivalence.  It does not assert literal
Move32Site equality and makes no cycle-impossibility or termination claim.
-/
theorem
    ClosedTriangulationCore.targetStar_equiv_of_sharedSupportedEdgeState_eq
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
    ∀ tau ∈ K.tets,
      (SameTetVertices tau anchor.targetTet₀ ∨
       SameTetVertices tau anchor.targetTet₁ ∨
       SameTetVertices tau anchor.targetTet₂) ↔
      (SameTetVertices tau ret.targetTet₀ ∨
       SameTetVertices tau ret.targetTet₁ ∨
       SameTetVertices tau ret.targetTet₂) := by
  classical

  have hanchorDistinct :
      anchor.d ≠ anchor.e :=
    (hcore.move32_sharedEdge_supported
      anchor
      hanchorRealized).2.2

  have hretDistinct :
      ret.d ≠ ret.e :=
    (hcore.move32_sharedEdge_supported
      ret
      hretRealized).2.2

  have hkey :
      canonicalEdgeKey anchor.d anchor.e =
        canonicalEdgeKey ret.d ret.e := by
    calc
      canonicalEdgeKey anchor.d anchor.e =
          (sharedSupportedEdgeState
            hcore
            anchor
            hanchorRealized).key :=
        (sharedSupportedEdgeState_key
          hcore
          anchor
          hanchorRealized).symm

      _ =
          (sharedSupportedEdgeState
            hcore
            ret
            hretRealized).key :=
        congrArg
          (fun q => q.key)
          hstate

      _ =
          canonicalEdgeKey ret.d ret.e :=
        sharedSupportedEdgeState_key
          hcore
          ret
          hretRealized

  have hendpoints :
      (anchor.d = ret.d ∧
       anchor.e = ret.e) ∨
      (anchor.d = ret.e ∧
       anchor.e = ret.d) :=
    (canonicalEdgeKey_eq_iff
      anchor.d
      anchor.e
      ret.d
      ret.e
      hanchorDistinct
      hretDistinct).mp hkey

  have hendpointsReverse :
      (ret.d = anchor.d ∧
       ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧
       ret.e = anchor.d) := by
    rcases hendpoints with
      hdirect | hreverse

    · exact
        Or.inl
          ⟨hdirect.1.symm,
            hdirect.2.symm⟩

    · exact
        Or.inr
          ⟨hreverse.2.symm,
            hreverse.1.symm⟩

  intro tau htauK

  constructor

  · intro hanchorTarget

    have hanchorD :
        anchor.d ∈ tau.verts := by
      rcases hanchorTarget with
        h0 | h1 | h2

      · apply (h0 anchor.d).2
        simp [
          Move32Site.targetTet₀,
          Tet.verts
        ]

      · apply (h1 anchor.d).2
        simp [
          Move32Site.targetTet₁,
          Tet.verts
        ]

      · apply (h2 anchor.d).2
        simp [
          Move32Site.targetTet₂,
          Tet.verts
        ]

    have hanchorE :
        anchor.e ∈ tau.verts := by
      rcases hanchorTarget with
        h0 | h1 | h2

      · apply (h0 anchor.e).2
        simp [
          Move32Site.targetTet₀,
          Tet.verts
        ]

      · apply (h1 anchor.e).2
        simp [
          Move32Site.targetTet₁,
          Tet.verts
        ]

      · apply (h2 anchor.e).2
        simp [
          Move32Site.targetTet₂,
          Tet.verts
        ]

    have hretD :
        ret.d ∈ tau.verts := by
      rcases hendpoints with
        hdirect | hreverse

      · exact
          hdirect.1 ▸ hanchorD

      · exact
          hreverse.2 ▸ hanchorE

    have hretE :
        ret.e ∈ tau.verts := by
      rcases hendpoints with
        hdirect | hreverse

      · exact
          hdirect.2 ▸ hanchorE

      · exact
          hreverse.1 ▸ hanchorD

    exact
      hcore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
        ret
        hretRealized
        hretThree
        htauK
        hretD
        hretE

  · intro hretTarget

    have hretD :
        ret.d ∈ tau.verts := by
      rcases hretTarget with
        h0 | h1 | h2

      · apply (h0 ret.d).2
        simp [
          Move32Site.targetTet₀,
          Tet.verts
        ]

      · apply (h1 ret.d).2
        simp [
          Move32Site.targetTet₁,
          Tet.verts
        ]

      · apply (h2 ret.d).2
        simp [
          Move32Site.targetTet₂,
          Tet.verts
        ]

    have hretE :
        ret.e ∈ tau.verts := by
      rcases hretTarget with
        h0 | h1 | h2

      · apply (h0 ret.e).2
        simp [
          Move32Site.targetTet₀,
          Tet.verts
        ]

      · apply (h1 ret.e).2
        simp [
          Move32Site.targetTet₁,
          Tet.verts
        ]

      · apply (h2 ret.e).2
        simp [
          Move32Site.targetTet₂,
          Tet.verts
        ]

    have hanchorD :
        anchor.d ∈ tau.verts := by
      rcases hendpointsReverse with
        hdirect | hreverse

      · exact
          hdirect.1 ▸ hretD

      · exact
          hreverse.2 ▸ hretE

    have hanchorE :
        anchor.e ∈ tau.verts := by
      rcases hendpointsReverse with
        hdirect | hreverse

      · exact
          hdirect.2 ▸ hretE

      · exact
          hreverse.1 ▸ hretD

    exact
      hcore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
        anchor
        hanchorRealized
        hanchorThree
        htauK
        hanchorD
        hanchorE

end Poincare
