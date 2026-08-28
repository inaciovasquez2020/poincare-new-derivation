import Poincare.GlobalMove32ReentryFirstNonzeroEarIncidence

namespace Poincare

/-- In the two-sided first-ear escape, the source vertex forced by the
southwest target excludes the matching target type for the compatibility
tetrahedron.  Thus `targetTet₁` with forced vertex `b` can transition only to
`targetTet₀` or `targetTet₂`, while `targetTet₂` with forced vertex `a` can
transition only to `targetTet₀` or `targetTet₁`.

This is only a target-family transition classification.  It does not assert a
represented source face, source-face absence, or Move32 legality. -/
theorem ClosedTriangulationCore.move32_firstEar_target_transition_probe
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (tau rho : Tet)
    (x : Nat)
    (hsource :
      (SameTetVertices tau s.targetTet₁ ∧ x = s.b) ∨
      (SameTetVertices tau s.targetTet₂ ∧ x = s.a))
    (hxRho : x ∈ rho.verts)
    (hrhoTarget :
      SameTetVertices rho s.targetTet₀ ∨
      SameTetVertices rho s.targetTet₁ ∨
      SameTetVertices rho s.targetTet₂) :
    (SameTetVertices tau s.targetTet₁ ∧ x = s.b ∧
        (SameTetVertices rho s.targetTet₀ ∨
          SameTetVertices rho s.targetTet₂)) ∨
      (SameTetVertices tau s.targetTet₂ ∧ x = s.a ∧
        (SameTetVertices rho s.targetTet₀ ∨
          SameTetVertices rho s.targetTet₁)) := by
  have hfive : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hrealized

  rcases hsource with h1 | h2
  · left
    refine ⟨h1.1, h1.2, ?_⟩
    rcases hrhoTarget with h0 | h1rho | h2rho
    · exact Or.inl h0
    · exfalso
      have hbTarget1 : s.b ∈ s.targetTet₁.verts :=
        (h1rho s.b).1 (by simpa [h1.2] using hxRho)
      simp [Move32Site.targetTet₁, Tet.verts] at hbTarget1
      simp at hfive
      omega
    · exact Or.inr h2rho

  · right
    refine ⟨h2.1, h2.2, ?_⟩
    rcases hrhoTarget with h0 | h1rho | h2rho
    · exact Or.inl h0
    · exact Or.inr h1rho
    · exfalso
      have haTarget2 : s.a ∈ s.targetTet₂.verts :=
        (h2rho s.a).1 (by simpa [h2.2] using hxRho)
      simp [Move32Site.targetTet₂, Tet.verts] at haTarget2
      simp at hfive
      omega

end Poincare
