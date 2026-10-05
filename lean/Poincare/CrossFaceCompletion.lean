    exact hrhone (hcore.eq_of_mem_of_sameTetVertices (τ := tau) (ρ := rho) htauK hrhoK hs).symm
  have hne' : ¬ SameTetVertices rho tau := by
    intro hs
    exact hne (by
      intro v
      exact (hs v).symm)
  obtain ⟨d, _, hdRho, hdout, _, _, _, hcoverRho, _⟩ :=
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
