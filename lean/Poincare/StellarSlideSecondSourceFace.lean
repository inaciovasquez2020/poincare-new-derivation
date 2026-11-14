import Poincare.StellarSlideSecondFace

namespace Poincare

/-- The second slide move contracts the edge from the original opposite
vertex to the fresh stellar center. -/
def Move41Site.slideSecond32 (s : Move41Site) : Move32Site :=
  { a := s.a, b := s.b, c := s.c, d := s.d, e := s.e }

/-- After the first canonical slide step, no tetrahedron contains the
three vertices of the face that the second 3→2 move will create.
The first six tetrahedra are checked explicitly, while the exterior
is excluded by the closed-core incidence theorem. -/
theorem Move41Site.slideSecond32_sourceFaceAbsent
    (s : Move41Site) (f : Nat) (rest : List Tet)
    (hfive : [s.a, s.b, s.c, s.e, f].Nodup)
    (hf : f ∉ [s.a, s.b, s.c, s.d, s.e])
    (hcore : ClosedTriangulationCore
      ({ tets := s.targetTet :: (⟨s.a, s.b, s.c, f⟩ : Tet) :: rest } :
        Triangulation)) :
    (s.slideSecond32).SourceFaceAbsent
      ((s.slideFirst23 f hfive).replace
        (s.headStellar ((⟨s.a, s.b, s.c, f⟩ : Tet) :: rest))) := by
  have hd := s.distinct
  have hext := s.slide_second_rest_face_absent f rest hcore
  intro τ hτ hface
  change s.a ∈ τ.verts ∧ s.b ∈ τ.verts ∧ s.c ∈ τ.verts at hface
  rw [s.slideFirst23_replace_canonical f rest hfive hf] at hτ
  simp only [List.mem_append] at hτ
  rcases hτ with hlocal | hrest
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlocal
    rcases hlocal with h0 | h1 | h2 | h3 | h4 | h5
    · rw [h0] at hface
      simp [Tet.verts] at hface
      simp_all
    · rw [h1] at hface
      simp [Tet.verts] at hface
      simp_all
    · rw [h2] at hface
      simp [Tet.verts] at hface
      simp_all
    · rw [h3] at hface
      simp [Tet.verts] at hface
      simp_all
    · rw [h4] at hface
      simp [Tet.verts] at hface
      simp_all
    · rw [h5] at hface
      simp [Tet.verts] at hface
      simp_all
  · exact hext τ hrest hface

end Poincare
