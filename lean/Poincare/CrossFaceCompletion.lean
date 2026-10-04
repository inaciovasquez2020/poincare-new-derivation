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
      exact hxy (by
        intro z
        constructor <;> intro hz <;> exact hz))
  have hfilterNodup : (K.tets.filter p).Nodup := hnodup.filter _
  have hneuw : u ≠ w := by
    have hfilterNodup' : [u, w].Nodup := by
      simpa [huw] using hfilterNodup
    have hu_not : u ∉ [w] := (List.nodup_cons.mp hfilterNodup').1
    intro huw'
    exact hu_not (by simp [huw'])
  have htauMem : tau ∈ K.tets.filter p := by
    simp [p, htauK, htauFace]
  rw [huw] at htauMem
  have htauCases : tau = u ∨ tau = w := by
    simpa using htauMem
  rcases htauCases with rfl | rfl
  · refine ⟨w, ?_, Ne.symm hneuw, ?_⟩
    · have hw : w ∈ K.tets.filter p := by
        rw [huw]
        simp
      exact (List.mem_filter.mp hw).1
    · have hw' : w ∈ K.tets.filter p := by
        rw [huw]
        simp
      simpa [p] using (List.mem_filter.mp hw').2
  · refine ⟨u, ?_, hneuw, ?_⟩
    · have hu : u ∈ K.tets.filter p := by
        rw [huw]
        simp
      exact (List.mem_filter.mp hu).1
    · have hu' : u ∈ K.tets.filter p := by
        rw [huw]
        simp
      simpa [p] using (List.mem_filter.mp hu').2


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
  obtain ⟨rho, hrhoK, hrhone, haRho, hbRho, hcRho⟩ :=
    hcore.exists_distinct_common_face_tet hface htauK htauFace
  have htauNodup : tau.verts.Nodup := hcore.1 tau htauK
  have hrhoNodup : rho.verts.Nodup := hcore.1 rho hrhoK
  have hne : ¬ SameTetVertices tau rho := by
    intro hs
    exact hrhone (hcore.eq_of_mem_of_sameTetVertices htauK hrhoK hs)
  have hne' : ¬ SameTetVertices rho tau := by
    intro hs
    exact hne (sameTetVertices_symm hs)
  obtain ⟨d, hdRho, hdout, _, _, hcoverRho⟩ :=
    Tet.exists_distinct_complement_vertices
      rho tau hrhoNodup htauNodup hface
      haRho hbRho hcRho htauFace.1 htauFace.2.1 htauFace.2.2
      hne'
  have hsame : SameTetVertices rho (⟨a, b, c, d⟩ : Tet) := by
    intro w
    constructor
    · intro hw
      rcases hcoverRho w hw with rfl | rfl | rfl | rfl <;>
        simp [Tet.verts]
    · intro hw
      simp [Tet.verts] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact haRho
      · exact hbRho
      · exact hcRho
      · exact hdRho
  exact ⟨rho, hrhoK, d, hrhone, hdRho, hdout, hsame⟩

end Poincare
