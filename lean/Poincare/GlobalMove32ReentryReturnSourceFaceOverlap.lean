import Poincare.GlobalMove32PerpetualWitnessedReentryRecurrentCrossing
import Mathlib.Tactic

namespace Poincare

/--
Suppose `sigma` is one of the target tetrahedra of an anchor Move32 site,
contains the shared edge of a realized incidence-three return site, and the
return shared edge is the same unordered edge as the anchor shared edge.

Then the anchor and return source faces have at least two distinct common
vertices.

This is the first source-face bridge extracted from a recurrent shared-edge
return.  It makes no cycle-impossibility or termination claim.
-/
theorem
    ClosedTriangulationCore.exists_two_common_sourceFace_vertices_of_return_target
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hretRealized : ret.RealizedIn K)
    (hretThree : ret.SharedEdgeExactlyThree K)
    {sigma : Tet}
    (hsigmaK : sigma ∈ K.tets)
    (hretD : ret.d ∈ sigma.verts)
    (hretE : ret.e ∈ sigma.verts)
    (hreturnEdge :
      (ret.d = anchor.d ∧
       ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧
       ret.e = anchor.d))
    (hanchorTarget :
      SameTetVertices sigma anchor.targetTet₀ ∨
      SameTetVertices sigma anchor.targetTet₁ ∨
      SameTetVertices sigma anchor.targetTet₂) :
    ∃ u v,
      u ≠ v ∧
      u ∈ [anchor.a, anchor.b, anchor.c] ∧
      v ∈ [anchor.a, anchor.b, anchor.c] ∧
      u ∈ [ret.a, ret.b, ret.c] ∧
      v ∈ [ret.a, ret.b, ret.c] := by
  classical

  have hretTarget :
      SameTetVertices sigma ret.targetTet₀ ∨
      SameTetVertices sigma ret.targetTet₁ ∨
      SameTetVertices sigma ret.targetTet₂ :=
    hcore.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
      ret
      hretRealized
      hretThree
      hsigmaK
      hretD
      hretE

  have hanchorFive :
      [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e].Nodup :=
    hcore.move32Site_distinct
      anchor
      hanchorRealized

  have hab :
      anchor.a ≠ anchor.b := by
    intro h
    rw [h] at hanchorFive
    simpa using hanchorFive

  have hac :
      anchor.a ≠ anchor.c := by
    intro h
    rw [h] at hanchorFive
    simpa using hanchorFive

  have hbc :
      anchor.b ≠ anchor.c := by
    intro h
    rw [h] at hanchorFive
    simpa using hanchorFive

  have haD :
      anchor.a ≠ anchor.d := by
    intro h
    rw [h] at hanchorFive
    simpa using hanchorFive

  have haE :
      anchor.a ≠ anchor.e := by
    intro h
    rw [h] at hanchorFive
    simpa using hanchorFive

  have hbD :
      anchor.b ≠ anchor.d := by
    intro h
    rw [h] at hanchorFive
    simpa using hanchorFive

  have hbE :
      anchor.b ≠ anchor.e := by
    intro h
    rw [h] at hanchorFive
    simpa using hanchorFive

  have hcD :
      anchor.c ≠ anchor.d := by
    intro h
    rw [h] at hanchorFive
    simpa using hanchorFive

  have hcE :
      anchor.c ≠ anchor.e := by
    intro h
    rw [h] at hanchorFive
    simpa using hanchorFive

  have hanchorSource_ne_retEdge
      {z : Nat}
      (hz :
        z ∈ [anchor.a, anchor.b, anchor.c]) :
      z ≠ ret.d ∧
      z ≠ ret.e := by
    simp only [
      List.mem_cons,
      List.not_mem_nil,
      or_false
    ] at hz

    rcases hz with
      rfl | rfl | rfl

    · rcases hreturnEdge with
        hdirect | hreverse

      · exact
          ⟨by
              simpa [hdirect.1] using haD,
            by
              simpa [hdirect.2] using haE⟩

      · exact
          ⟨by
              simpa [hreverse.1] using haE,
            by
              simpa [hreverse.2] using haD⟩

    · rcases hreturnEdge with
        hdirect | hreverse

      · exact
          ⟨by
              simpa [hdirect.1] using hbD,
            by
              simpa [hdirect.2] using hbE⟩

      · exact
          ⟨by
              simpa [hreverse.1] using hbE,
            by
              simpa [hreverse.2] using hbD⟩

    · rcases hreturnEdge with
        hdirect | hreverse

      · exact
          ⟨by
              simpa [hdirect.1] using hcD,
            by
              simpa [hdirect.2] using hcE⟩

      · exact
          ⟨by
              simpa [hreverse.1] using hcE,
            by
              simpa [hreverse.2] using hcD⟩

  have hretSource_of_mem_sigma
      {z : Nat}
      (hzSigma : z ∈ sigma.verts)
      (hzd : z ≠ ret.d)
      (hze : z ≠ ret.e) :
      z ∈ [ret.a, ret.b, ret.c] := by

    rcases hretTarget with
      ht0 | ht1 | ht2

    · have hzTarget :
          z ∈ ret.targetTet₀.verts :=
        (ht0 z).1 hzSigma

      simp only [
        Move32Site.targetTet₀,
        Tet.verts,
        List.mem_cons,
        List.mem_singleton
      ] at hzTarget ⊢

      aesop

    · have hzTarget :
          z ∈ ret.targetTet₁.verts :=
        (ht1 z).1 hzSigma

      simp only [
        Move32Site.targetTet₁,
        Tet.verts,
        List.mem_cons,
        List.mem_singleton
      ] at hzTarget ⊢

      aesop

    · have hzTarget :
          z ∈ ret.targetTet₂.verts :=
        (ht2 z).1 hzSigma

      simp only [
        Move32Site.targetTet₂,
        Tet.verts,
        List.mem_cons,
        List.mem_singleton
      ] at hzTarget ⊢

      aesop

  rcases hanchorTarget with
    ht0 | ht1 | ht2

  · have haSigma :
        anchor.a ∈ sigma.verts := by
      apply (ht0 anchor.a).2
      simp [
        Move32Site.targetTet₀,
        Tet.verts
      ]

    have hbSigma :
        anchor.b ∈ sigma.verts := by
      apply (ht0 anchor.b).2
      simp [
        Move32Site.targetTet₀,
        Tet.verts
      ]

    have haRetEdge :=
      hanchorSource_ne_retEdge
        (z := anchor.a)
        (by simp)

    have hbRetEdge :=
      hanchorSource_ne_retEdge
        (z := anchor.b)
        (by simp)

    have haRetSource :
        anchor.a ∈
          [ret.a, ret.b, ret.c] :=
      hretSource_of_mem_sigma
        haSigma
        haRetEdge.1
        haRetEdge.2

    have hbRetSource :
        anchor.b ∈
          [ret.a, ret.b, ret.c] :=
      hretSource_of_mem_sigma
        hbSigma
        hbRetEdge.1
        hbRetEdge.2

    exact
      ⟨anchor.a,
        anchor.b,
        hab,
        by simp,
        by simp,
        haRetSource,
        hbRetSource⟩

  · have haSigma :
        anchor.a ∈ sigma.verts := by
      apply (ht1 anchor.a).2
      simp [
        Move32Site.targetTet₁,
        Tet.verts
      ]

    have hcSigma :
        anchor.c ∈ sigma.verts := by
      apply (ht1 anchor.c).2
      simp [
        Move32Site.targetTet₁,
        Tet.verts
      ]

    have haRetEdge :=
      hanchorSource_ne_retEdge
        (z := anchor.a)
        (by simp)

    have hcRetEdge :=
      hanchorSource_ne_retEdge
        (z := anchor.c)
        (by simp)

    have haRetSource :
        anchor.a ∈
          [ret.a, ret.b, ret.c] :=
      hretSource_of_mem_sigma
        haSigma
        haRetEdge.1
        haRetEdge.2

    have hcRetSource :
        anchor.c ∈
          [ret.a, ret.b, ret.c] :=
      hretSource_of_mem_sigma
        hcSigma
        hcRetEdge.1
        hcRetEdge.2

    exact
      ⟨anchor.a,
        anchor.c,
        hac,
        by simp,
        by simp,
        haRetSource,
        hcRetSource⟩

  · have hbSigma :
        anchor.b ∈ sigma.verts := by
      apply (ht2 anchor.b).2
      simp [
        Move32Site.targetTet₂,
        Tet.verts
      ]

    have hcSigma :
        anchor.c ∈ sigma.verts := by
      apply (ht2 anchor.c).2
      simp [
        Move32Site.targetTet₂,
        Tet.verts
      ]

    have hbRetEdge :=
      hanchorSource_ne_retEdge
        (z := anchor.b)
        (by simp)

    have hcRetEdge :=
      hanchorSource_ne_retEdge
        (z := anchor.c)
        (by simp)

    have hbRetSource :
        anchor.b ∈
          [ret.a, ret.b, ret.c] :=
      hretSource_of_mem_sigma
        hbSigma
        hbRetEdge.1
        hbRetEdge.2

    have hcRetSource :
        anchor.c ∈
          [ret.a, ret.b, ret.c] :=
      hretSource_of_mem_sigma
        hcSigma
        hcRetEdge.1
        hcRetEdge.2

    exact
      ⟨anchor.b,
        anchor.c,
        hbc,
        by simp,
        by simp,
        hbRetSource,
        hcRetSource⟩

end Poincare
