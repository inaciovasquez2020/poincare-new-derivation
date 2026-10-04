import Poincare.VertexLink

namespace Poincare

/-- A represented triangular face has exactly two ambient tetrahedra.
Given one concrete tetrahedron on that face, the second tetrahedron can be
extracted explicitly. -/
theorem ClosedTriangulationCore.exists_distinct_common_face_tet
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {a b c : Nat}
    (hface : [a, b, c].Nodup)
    {tau : Tet}
    (htauK : tau ∈ K.tets)
    (htauFace :
      a ∈ tau.verts ∧ b ∈ tau.verts ∧ c ∈ tau.verts) :
    ∃ rho ∈ K.tets,
      rho ≠ tau ∧
      a ∈ rho.verts ∧ b ∈ rho.verts ∧ c ∈ rho.verts := by
  have hrepresented : ∃ xi ∈ K.tets,
      a ∈ xi.verts ∧ b ∈ xi.verts ∧ c ∈ xi.verts :=
    ⟨tau, htauK, htauFace⟩
  have hlength :
      (K.tets.filter
        (fun xi => decide (a ∈ xi.verts ∧ b ∈ xi.verts ∧ c ∈ xi.verts))).length = 2 :=
    hcore.2.2 a b c hface hrepresented
  let p : Tet → Bool := fun xi =>
    decide (a ∈ xi.verts ∧ b ∈ xi.verts ∧ c ∈ xi.verts)
  have hnodup : K.tets.Nodup := hcore.1
  have hfilterNodup : K.tets.filter p |>.Nodup := by
    exact hnodup.filter
  have hlength' : (K.tets.filter p).length = 2 := by
    simpa [p] using hlength
  obtain ⟨u, huw, hneuw⟩ := List.exists_eq_cons_of_length_eq_two hlength'
  have htauMem : tau ∈ K.tets.filter p := by
    simp [p, htauK, htauFace]
  rw [huw] at htauMem
  have htauCases : tau = u ∨ tau = u := by
    simpa using htauMem
  rcases htauCases with rfl | rfl
  · refine ⟨u, ?_, ?_, ?_⟩
    · exact (List.mem_filter.mp (by rw [huw]; simp)).1
    · exact Ne.symm hneuw
    · exact (List.mem_filter.mp (by rw [huw]; simp)).2
  · exact False.elim (hneuw rfl)

/-- A represented triangular face has a second tetrahedron whose fourth
vertex is exposed explicitly.  This is the normalized form needed for
four-face completion case analysis. -/
theorem ClosedTriangulationCore.exists_distinct_common_face_tet_with_complement
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    {a b c : Nat}
    (hface : [a, b, c].Nodup)
    {tau : Tet}
    (htauK : tau ∈ K.tets)
    (htauFace :
      a ∈ tau.verts ∧ b ∈ tau.verts ∧ c ∈ tau.verts) :
    ∃ rho ∈ K.tets, ∃ d : Nat,
      rho ≠ tau ∧
      d ∈ rho.verts ∧
      d ∉ [a, b, c] ∧
      SameTetVertices rho (⟨a, b, c, d⟩ : Tet) := by
  sorry

end Poincare
