import Poincare.GlobalMove32ReentryPolygonalLoopAnchorObstruction

namespace Poincare

/--
Under the fail-closed high-incidence exclusion, any represented anchor cross
edge from `{a,b} × {d,e}` cannot lie in four or more represented tetrahedra.
Thus an incidence split `= 3 ∨ ≥ 4` for such a cross edge collapses to exact
incidence three.

This eliminates only the high-incidence half of the one-sided first-ear fork.
It does not eliminate cancellation, two-sided target transition, or the
remaining exact-incidence-three branch.
-/
theorem WitnessedReentryPolygonalLoopCertificate.anchor_crossEdge_incidence_eq_three_of_split_of_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (p : WitnessedReentryPolygonalLoopCertificate K)
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
    {v x : Nat}
    (hcross :
      (v = (p.crossing.sites p.crossing.anchorIndex).b ∧
          x = (p.crossing.sites p.crossing.anchorIndex).d) ∨
        (v = (p.crossing.sites p.crossing.anchorIndex).b ∧
          x = (p.crossing.sites p.crossing.anchorIndex).e) ∨
        (v = (p.crossing.sites p.crossing.anchorIndex).a ∧
          x = (p.crossing.sites p.crossing.anchorIndex).d) ∨
        (v = (p.crossing.sites p.crossing.anchorIndex).a ∧
          x = (p.crossing.sites p.crossing.anchorIndex).e))
    {rho : Tet}
    (hrho : rho ∈ K.tets)
    (hvRho : v ∈ rho.verts)
    (hxRho : x ∈ rho.verts)
    (hinc :
      (K.tets.filter
          (fun sigma => v ∈ sigma.verts ∧ x ∈ sigma.verts)).length = 3 ∨
        4 ≤
          (K.tets.filter
            (fun sigma => v ∈ sigma.verts ∧ x ∈ sigma.verts)).length) :
    (K.tets.filter
        (fun sigma => v ∈ sigma.verts ∧ x ∈ sigma.verts)).length = 3 := by
  let s : Move32Site := p.crossing.sites p.crossing.anchorIndex

  have hsRealized : s.RealizedIn K := by
    simpa [s] using p.realized p.crossing.anchorIndex

  have hsource :
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts := by
    simpa [s] using p.anchor_sourceFace_obstruction

  have hdistinct : [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hsRealized

  have hbD : s.b ≠ s.d := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have hbE : s.b ≠ s.e := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have haD : s.a ≠ s.d := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have haE : s.a ≠ s.e := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  rcases hinc with hthree | hhigh
  · exact hthree

  exfalso

  have hvx : v ≠ x := by
    rcases hcross with h | h | h | h
    · simpa [s, h.1, h.2] using hbD
    · simpa [s, h.1, h.2] using hbE
    · simpa [s, h.1, h.2] using haD
    · simpa [s, h.1, h.2] using haE

  have hnonself :
      ¬ ((v = s.d ∧ x = s.e) ∨
         (v = s.e ∧ x = s.d)) := by
    rcases hcross with h | h | h | h
    · subst v
      subst x
      simp [s, hbD, hbE]
    · subst v
      subst x
      simp [s, hbD, hbE]
    · subst v
      subst x
      simp [s, haD, haE]
    · subst v
      subst x
      simp [s, haD, haE]

  have hhighDecide :
      4 ≤
        (K.tets.filter
          (fun gamma =>
            decide (v ∈ gamma.verts ∧ x ∈ gamma.verts))).length := by
    simpa using hhigh

  exact
    (hNoHigh s hsRealized hsource)
      ⟨v, x, rho, hvx, hrho, hvRho, hxRho, hnonself, hhighDecide⟩

end Poincare
