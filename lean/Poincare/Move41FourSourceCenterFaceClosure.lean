import Poincare.Move41FourSourceCenterDegree
import Poincare.DegreeFourConnectedLinkClassification

namespace Poincare

/--
For four concrete represented tetrahedra realizing the four sources of a
Move41 site, every represented triangular face containing the center has its
closed-core partner among the same four source tetrahedra.

The opposite target tetrahedron is unnecessary: the unique face of a source
tetrahedron opposite the center does not contain the center.
-/
theorem Move41Site.represented_sourceCluster_closed_under_center_face
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move41Site)
    {tau₀ tau₁ tau₂ tau₃ : Tet}
    (htau₀K : tau₀ ∈ K.tets)
    (htau₀ : SameTetVertices tau₀ s.sourceTet₀)
    (htau₁K : tau₁ ∈ K.tets)
    (htau₁ : SameTetVertices tau₁ s.sourceTet₁)
    (htau₂K : tau₂ ∈ K.tets)
    (htau₂ : SameTetVertices tau₂ s.sourceTet₂)
    (htau₃K : tau₃ ∈ K.tets)
    (htau₃ : SameTetVertices tau₃ s.sourceTet₃)
    (hnodup : [tau₀, tau₁, tau₂, tau₃].Nodup) :
    ∀ alpha sigma x y,
      (alpha = tau₀ ∨ alpha = tau₁ ∨
        alpha = tau₂ ∨ alpha = tau₃) →
      sigma ∈ K.tets →
      [s.e, x, y].Nodup →
      (s.e ∈ alpha.verts ∧
        x ∈ alpha.verts ∧
        y ∈ alpha.verts) →
      (s.e ∈ sigma.verts ∧
        x ∈ sigma.verts ∧
        y ∈ sigma.verts) →
      (sigma = tau₀ ∨ sigma = tau₁ ∨
        sigma = tau₂ ∨ sigma = tau₃) := by
  classical

  let cluster : List Tet := [tau₀, tau₁, tau₂, tau₃]

  have h01 : tau₀ ≠ tau₁ := by
    intro h
    subst tau₁
    simpa using hnodup

  have h02 : tau₀ ≠ tau₂ := by
    intro h
    subst tau₂
    simpa using hnodup

  have h03 : tau₀ ≠ tau₃ := by
    intro h
    subst tau₃
    simpa using hnodup

  have h12 : tau₁ ≠ tau₂ := by
    intro h
    subst tau₂
    simpa using hnodup

  have h13 : tau₁ ≠ tau₃ := by
    intro h
    subst tau₃
    simpa using hnodup

  have h23 : tau₂ ≠ tau₃ := by
    intro h
    subst tau₃
    simpa using hnodup

  have liftFace
      {x y z u v w : Nat}
      {beta model : Tet}
      (hrep : SameTetVertices beta model)
      (hu : u ∈ model.verts)
      (hv : v ∈ model.verts)
      (hw : w ∈ model.verts)
      (hface :
        ∀ q,
          (q = x ∨ q = y ∨ q = z) ↔
          (q = u ∨ q = v ∨ q = w)) :
      x ∈ beta.verts ∧
        y ∈ beta.verts ∧
        z ∈ beta.verts := by
    have hx : x = u ∨ x = v ∨ x = w :=
      (hface x).1 (Or.inl rfl)
    have hy : y = u ∨ y = v ∨ y = w :=
      (hface y).1 (Or.inr (Or.inl rfl))
    have hz : z = u ∨ z = v ∨ z = w :=
      (hface z).1 (Or.inr (Or.inr rfl))
    refine ⟨?_, ?_, ?_⟩
    · apply (hrep x).2
      rcases hx with rfl | rfl | rfl <;> assumption
    · apply (hrep y).2
      rcases hy with rfl | rfl | rfl <;> assumption
    · apply (hrep z).2
      rcases hz with rfl | rfl | rfl <;> assumption

  have center_not_outer :
      s.e ≠ s.a ∧
      s.e ≠ s.b ∧
      s.e ≠ s.c ∧
      s.e ≠ s.d := by
    have hd := s.distinct
    simp at hd
    aesop

  have partner0 :
      ∀ x y,
        [s.e, x, y].Nodup →
        (s.e ∈ tau₀.verts ∧
          x ∈ tau₀.verts ∧
          y ∈ tau₀.verts) →
        ∃ beta,
          beta ∈ cluster ∧
          beta ≠ tau₀ ∧
          beta ∈ K.tets ∧
          (s.e ∈ beta.verts ∧
            x ∈ beta.verts ∧
            y ∈ beta.verts) := by
    intro x y hxyz hface

    have he := (htau₀ s.e).1 hface.1
    have hx := (htau₀ x).1 hface.2.1
    have hy := (htau₀ y).1 hface.2.2

    rcases
        Tet.distinct_triple_face_cases
          s.sourceTet₀ s.e x y hxyz he hx hy
      with h | h | h | h

    · refine ⟨tau₃, by simp [cluster], Ne.symm h03, htau₃K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.b) (v := s.c) (w := s.e)
        htau₃
        (by simp [Move41Site.sourceTet₃, Tet.verts])
        (by simp [Move41Site.sourceTet₃, Tet.verts])
        (by simp [Move41Site.sourceTet₃, Tet.verts])
        (by simpa [Move41Site.sourceTet₀] using h)

    · refine ⟨tau₂, by simp [cluster], Ne.symm h02, htau₂K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.a) (v := s.c) (w := s.e)
        htau₂
        (by simp [Move41Site.sourceTet₂, Tet.verts])
        (by simp [Move41Site.sourceTet₂, Tet.verts])
        (by simp [Move41Site.sourceTet₂, Tet.verts])
        (by simpa [Move41Site.sourceTet₀] using h)

    · refine ⟨tau₁, by simp [cluster], Ne.symm h01, htau₁K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.a) (v := s.b) (w := s.e)
        htau₁
        (by simp [Move41Site.sourceTet₁, Tet.verts])
        (by simp [Move41Site.sourceTet₁, Tet.verts])
        (by simp [Move41Site.sourceTet₁, Tet.verts])
        (by simpa [Move41Site.sourceTet₀] using h)

    · have heabc :
          s.e = s.a ∨ s.e = s.b ∨ s.e = s.c :=
        (h s.e).1 (Or.inl rfl)
      rcases heabc with hea | heb | hec
      · exact (center_not_outer.1 hea).elim
      · exact (center_not_outer.2.1 heb).elim
      · exact (center_not_outer.2.2.1 hec).elim

  have partner1 :
      ∀ x y,
        [s.e, x, y].Nodup →
        (s.e ∈ tau₁.verts ∧
          x ∈ tau₁.verts ∧
          y ∈ tau₁.verts) →
        ∃ beta,
          beta ∈ cluster ∧
          beta ≠ tau₁ ∧
          beta ∈ K.tets ∧
          (s.e ∈ beta.verts ∧
            x ∈ beta.verts ∧
            y ∈ beta.verts) := by
    intro x y hxyz hface

    have he := (htau₁ s.e).1 hface.1
    have hx := (htau₁ x).1 hface.2.1
    have hy := (htau₁ y).1 hface.2.2

    rcases
        Tet.distinct_triple_face_cases
          s.sourceTet₁ s.e x y hxyz he hx hy
      with h | h | h | h

    · refine ⟨tau₃, by simp [cluster], Ne.symm h13, htau₃K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.b) (v := s.d) (w := s.e)
        htau₃
        (by simp [Move41Site.sourceTet₃, Tet.verts])
        (by simp [Move41Site.sourceTet₃, Tet.verts])
        (by simp [Move41Site.sourceTet₃, Tet.verts])
        (by simpa [Move41Site.sourceTet₁] using h)

    · refine ⟨tau₂, by simp [cluster], Ne.symm h12, htau₂K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.a) (v := s.d) (w := s.e)
        htau₂
        (by simp [Move41Site.sourceTet₂, Tet.verts])
        (by simp [Move41Site.sourceTet₂, Tet.verts])
        (by simp [Move41Site.sourceTet₂, Tet.verts])
        (by simpa [Move41Site.sourceTet₁] using h)

    · refine ⟨tau₀, by simp [cluster], h01, htau₀K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.a) (v := s.b) (w := s.e)
        htau₀
        (by simp [Move41Site.sourceTet₀, Tet.verts])
        (by simp [Move41Site.sourceTet₀, Tet.verts])
        (by simp [Move41Site.sourceTet₀, Tet.verts])
        (by simpa [Move41Site.sourceTet₁] using h)

    · have heabd :
          s.e = s.a ∨ s.e = s.b ∨ s.e = s.d :=
        (h s.e).1 (Or.inl rfl)
      rcases heabd with hea | heb | hed
      · exact (center_not_outer.1 hea).elim
      · exact (center_not_outer.2.1 heb).elim
      · exact (center_not_outer.2.2.2 hed).elim

  have partner2 :
      ∀ x y,
        [s.e, x, y].Nodup →
        (s.e ∈ tau₂.verts ∧
          x ∈ tau₂.verts ∧
          y ∈ tau₂.verts) →
        ∃ beta,
          beta ∈ cluster ∧
          beta ≠ tau₂ ∧
          beta ∈ K.tets ∧
          (s.e ∈ beta.verts ∧
            x ∈ beta.verts ∧
            y ∈ beta.verts) := by
    intro x y hxyz hface

    have he := (htau₂ s.e).1 hface.1
    have hx := (htau₂ x).1 hface.2.1
    have hy := (htau₂ y).1 hface.2.2

    rcases
        Tet.distinct_triple_face_cases
          s.sourceTet₂ s.e x y hxyz he hx hy
      with h | h | h | h

    · refine ⟨tau₃, by simp [cluster], Ne.symm h23, htau₃K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.c) (v := s.d) (w := s.e)
        htau₃
        (by simp [Move41Site.sourceTet₃, Tet.verts])
        (by simp [Move41Site.sourceTet₃, Tet.verts])
        (by simp [Move41Site.sourceTet₃, Tet.verts])
        (by simpa [Move41Site.sourceTet₂] using h)

    · refine ⟨tau₁, by simp [cluster], h12, htau₁K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.a) (v := s.d) (w := s.e)
        htau₁
        (by simp [Move41Site.sourceTet₁, Tet.verts])
        (by simp [Move41Site.sourceTet₁, Tet.verts])
        (by simp [Move41Site.sourceTet₁, Tet.verts])
        (by simpa [Move41Site.sourceTet₂] using h)

    · refine ⟨tau₀, by simp [cluster], h02, htau₀K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.a) (v := s.c) (w := s.e)
        htau₀
        (by simp [Move41Site.sourceTet₀, Tet.verts])
        (by simp [Move41Site.sourceTet₀, Tet.verts])
        (by simp [Move41Site.sourceTet₀, Tet.verts])
        (by simpa [Move41Site.sourceTet₂] using h)

    · have heacd :
          s.e = s.a ∨ s.e = s.c ∨ s.e = s.d :=
        (h s.e).1 (Or.inl rfl)
      rcases heacd with hea | hec | hed
      · exact (center_not_outer.1 hea).elim
      · exact (center_not_outer.2.2.1 hec).elim
      · exact (center_not_outer.2.2.2 hed).elim

  have partner3 :
      ∀ x y,
        [s.e, x, y].Nodup →
        (s.e ∈ tau₃.verts ∧
          x ∈ tau₃.verts ∧
          y ∈ tau₃.verts) →
        ∃ beta,
          beta ∈ cluster ∧
          beta ≠ tau₃ ∧
          beta ∈ K.tets ∧
          (s.e ∈ beta.verts ∧
            x ∈ beta.verts ∧
            y ∈ beta.verts) := by
    intro x y hxyz hface

    have he := (htau₃ s.e).1 hface.1
    have hx := (htau₃ x).1 hface.2.1
    have hy := (htau₃ y).1 hface.2.2

    rcases
        Tet.distinct_triple_face_cases
          s.sourceTet₃ s.e x y hxyz he hx hy
      with h | h | h | h

    · refine ⟨tau₂, by simp [cluster], h23, htau₂K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.c) (v := s.d) (w := s.e)
        htau₂
        (by simp [Move41Site.sourceTet₂, Tet.verts])
        (by simp [Move41Site.sourceTet₂, Tet.verts])
        (by simp [Move41Site.sourceTet₂, Tet.verts])
        (by simpa [Move41Site.sourceTet₃] using h)

    · refine ⟨tau₁, by simp [cluster], h13, htau₁K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.b) (v := s.d) (w := s.e)
        htau₁
        (by simp [Move41Site.sourceTet₁, Tet.verts])
        (by simp [Move41Site.sourceTet₁, Tet.verts])
        (by simp [Move41Site.sourceTet₁, Tet.verts])
        (by simpa [Move41Site.sourceTet₃] using h)

    · refine ⟨tau₀, by simp [cluster], h03, htau₀K, ?_⟩
      exact liftFace
        (x := s.e) (y := x) (z := y)
        (u := s.b) (v := s.c) (w := s.e)
        htau₀
        (by simp [Move41Site.sourceTet₀, Tet.verts])
        (by simp [Move41Site.sourceTet₀, Tet.verts])
        (by simp [Move41Site.sourceTet₀, Tet.verts])
        (by simpa [Move41Site.sourceTet₃] using h)

    · have hebcd :
          s.e = s.b ∨ s.e = s.c ∨ s.e = s.d :=
        (h s.e).1 (Or.inl rfl)
      rcases hebcd with heb | hec | hed
      · exact (center_not_outer.2.1 heb).elim
      · exact (center_not_outer.2.2.1 hec).elim
      · exact (center_not_outer.2.2.2 hed).elim

  have hpartner :
      ∀ alpha x y,
        alpha ∈ cluster →
        [s.e, x, y].Nodup →
        (s.e ∈ alpha.verts ∧
          x ∈ alpha.verts ∧
          y ∈ alpha.verts) →
        ∃ beta,
          beta ∈ cluster ∧
          beta ≠ alpha ∧
          beta ∈ K.tets ∧
          (s.e ∈ beta.verts ∧
            x ∈ beta.verts ∧
            y ∈ beta.verts) := by
    intro alpha x y halpha hxyz hface
    simp [cluster] at halpha
    rcases halpha with rfl | rfl | rfl | rfl
    · exact partner0 x y hxyz hface
    · exact partner1 x y hxyz hface
    · exact partner2 x y hxyz hface
    · exact partner3 x y hxyz hface

  intro alpha sigma x y
    halpha hsigmaK hxyz halphaFace hsigmaFace

  have halphaMem : alpha ∈ cluster := by
    simpa [cluster] using halpha

  obtain
      ⟨beta, hbetaMem, hbetaNeAlpha,
        hbetaK, hbetaFace⟩ :=
    hpartner alpha x y halphaMem hxyz halphaFace

  have halphaK : alpha ∈ K.tets := by
    rcases halpha with rfl | rfl | rfl | rfl <;>
      assumption

  rcases
      hcore.eq_left_or_eq_right_of_common_face
        hxyz
        halphaK
        hbetaK
        halphaFace
        hbetaFace
        (Ne.symm hbetaNeAlpha)
        hsigmaK
        hsigmaFace
    with hsigma | hsigma

  · subst sigma
    exact halpha

  · subst sigma
    simpa [cluster] using hbetaMem

end Poincare
