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
  classical
  let p : Tet → Bool := fun xi =>
    decide (a ∈ xi.verts ∧ b ∈ xi.verts ∧ c ∈ xi.verts)
  have hrepresented :
      ∃ xi ∈ K.tets,
        a ∈ xi.verts ∧ b ∈ xi.verts ∧ c ∈ xi.verts :=
    ⟨tau, htauK, htauFace⟩
  have hlength : (K.tets.filter p).length = 2 := by
    simpa [p] using hcore.2.2 a b c hface hrepresented
  obtain ⟨u, w, huw⟩ := List.length_eq_two.mp hlength
  have hnodup : K.tets.Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hcore.2.1.imp (fun {x y} hxy heq => by
      subst y
      exact hxy (sameTetVertices_refl x))
  have hfilterNodup : (K.tets.filter p).Nodup := hnodup.filter _
  have hneuw : u ≠ w := by
    intro huw'
    subst w
    exact hfilterNodup (by simpa [huw'])
  have htauMem : tau ∈ K.tets.filter p := by
    simp [p, htauK, htauFace]
  rw [huw] at htauMem
  have htauCases : tau = u ∨ tau = w := by
    simpa using htauMem
  rcases htauCases with rfl | rfl
  · refine ⟨w, ?_, hneuw, ?_⟩
    · have : w ∈ [u, w] := by simp
      rw [← huw]
      exact (List.mem_filter.mp this).1
    · have : w ∈ [u, w] := by simp
      rw [← huw]
      exact (List.mem_filter.mp this).2
  · refine ⟨u, ?_, Ne.symm hneuw, ?_⟩
    · have : u ∈ [u, w] := by simp
      rw [← huw]
      exact (List.mem_filter.mp this).1
    · have : u ∈ [u, w] := by simp
      rw [← huw]
      exact (List.mem_filter.mp this).2

end Poincare
