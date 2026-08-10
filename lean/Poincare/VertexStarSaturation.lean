import Poincare.ComplementVertex
import Poincare.VertexIncidenceCounting

namespace Poincare

private theorem sameTetVertices_of_contains_fields
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {τ ρ : Tet} (hτ : τ.verts.Nodup) (hρK : ρ ∈ K.tets)
    (h0 : τ.v0 ∈ ρ.verts) (h1 : τ.v1 ∈ ρ.verts)
    (h2 : τ.v2 ∈ ρ.verts) (h3 : τ.v3 ∈ ρ.verts) :
    SameTetVertices τ ρ := by
  have hρ := hcore.1 ρ hρK
  have hsub : τ.verts.toFinset ⊆ ρ.verts.toFinset := by
    intro v hv
    simp [Tet.verts] at hv ⊢
    rcases hv with rfl | rfl | rfl | rfl
    · simpa [Tet.verts] using h0
    · simpa [Tet.verts] using h1
    · simpa [Tet.verts] using h2
    · simpa [Tet.verts] using h3
  have hcardτ : τ.verts.toFinset.card = 4 := by
    simpa [Tet.verts] using List.toFinset_card_of_nodup hτ
  have hcardρ : ρ.verts.toFinset.card = 4 := by
    simpa [Tet.verts] using List.toFinset_card_of_nodup hρ
  have heq : τ.verts.toFinset = ρ.verts.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro v
  simpa using Finset.ext_iff.mp heq v

/-- At zero support defect, the four tetrahedra obtained from a tetrahedron and
the three faces through its first vertex exhaust the star of that vertex. -/
theorem ClosedTriangulationCore.exists_vertex_star_saturation
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hPhi : PhiSupport K = 0)
    {τ : Tet}
    (hτK : τ ∈ K.tets)
    (hτ : τ.verts.Nodup) :
    ∃ ρ012 ρ013 ρ023,
      ρ012 ∈ K.tets ∧ ρ013 ∈ K.tets ∧ ρ023 ∈ K.tets ∧
      τ.v0 ∈ ρ012.verts ∧ τ.v1 ∈ ρ012.verts ∧ τ.v2 ∈ ρ012.verts ∧
      τ.v0 ∈ ρ013.verts ∧ τ.v1 ∈ ρ013.verts ∧ τ.v3 ∈ ρ013.verts ∧
      τ.v0 ∈ ρ023.verts ∧ τ.v2 ∈ ρ023.verts ∧ τ.v3 ∈ ρ023.verts ∧
      ¬ SameTetVertices τ ρ012 ∧
      ¬ SameTetVertices τ ρ013 ∧
      ¬ SameTetVertices τ ρ023 ∧
      τ ≠ ρ012 ∧ τ ≠ ρ013 ∧ τ ≠ ρ023 ∧
      ρ012 ≠ ρ013 ∧ ρ012 ≠ ρ023 ∧ ρ013 ≠ ρ023 ∧
      ∀ σ ∈ K.tets, τ.v0 ∈ σ.verts →
        σ = τ ∨ σ = ρ012 ∨ σ = ρ013 ∨ σ = ρ023 := by
  classical
  have h012 : [τ.v0, τ.v1, τ.v2].Nodup := by
    simp [Tet.verts] at hτ ⊢
    aesop
  have h013 : [τ.v0, τ.v1, τ.v3].Nodup := by
    simp [Tet.verts] at hτ ⊢
    aesop
  have h023 : [τ.v0, τ.v2, τ.v3].Nodup := by
    simp [Tet.verts] at hτ ⊢
    aesop
  obtain ⟨ρ012, hρ012K, hn012, h0_012, h1_012, h2_012⟩ :=
    hcore.exists_other_tet_across_triangle h012 hτK
      (by simp [Tet.verts]) (by simp [Tet.verts]) (by simp [Tet.verts])
  obtain ⟨ρ013, hρ013K, hn013, h0_013, h1_013, h3_013⟩ :=
    hcore.exists_other_tet_across_triangle h013 hτK
      (by simp [Tet.verts]) (by simp [Tet.verts]) (by simp [Tet.verts])
  obtain ⟨ρ023, hρ023K, hn023, h0_023, h2_023, h3_023⟩ :=
    hcore.exists_other_tet_across_triangle h023 hτK
      (by simp [Tet.verts]) (by simp [Tet.verts]) (by simp [Tet.verts])
  have hτ012 : τ ≠ ρ012 := by
    intro h
    apply hn012
    subst ρ012
    intro v
    rfl
  have hτ013 : τ ≠ ρ013 := by
    intro h
    apply hn013
    subst ρ013
    intro v
    rfl
  have hτ023 : τ ≠ ρ023 := by
    intro h
    apply hn023
    subst ρ023
    intro v
    rfl
  have h012013 : ρ012 ≠ ρ013 := by
    intro h
    apply hn012
    subst ρ013
    exact sameTetVertices_of_contains_fields hcore hτ hρ012K
      h0_012 h1_012 h2_012 h3_013
  have h012023 : ρ012 ≠ ρ023 := by
    intro h
    apply hn012
    subst ρ023
    exact sameTetVertices_of_contains_fields hcore hτ hρ012K
      h0_012 h1_012 h2_012 h3_023
  have h013023 : ρ013 ≠ ρ023 := by
    intro h
    apply hn013
    subst ρ023
    exact sameTetVertices_of_contains_fields hcore hτ hρ013K
      h0_013 h1_013 h2_023 h3_013
  let incident := K.tets.filter (fun σ => τ.v0 ∈ σ.verts)
  have hincLength : incident.length = 4 := by
    apply hcore.incidentTetCount_eq_four_of_PhiSupport_eq_zero hPhi
    apply (mem_vertexSupport_iff K τ.v0).2
    apply List.mem_flatMap.mpr
    exact ⟨τ, hτK, by simp [Tet.verts]⟩
  have hincNodup : incident.Nodup := by
    apply List.Nodup.filter
    exact hcore.2.1.imp (by
      intro σ ρ hne hEq
      apply hne
      subst ρ
      intro v
      rfl)
  have hmemτ : τ ∈ incident := by simp [incident, hτK, Tet.verts]
  have hmem012 : ρ012 ∈ incident := by simp [incident, hρ012K, h0_012]
  have hmem013 : ρ013 ∈ incident := by simp [incident, hρ013K, h0_013]
  have hmem023 : ρ023 ∈ incident := by simp [incident, hρ023K, h0_023]
  refine ⟨ρ012, ρ013, ρ023, hρ012K, hρ013K, hρ023K,
    h0_012, h1_012, h2_012, h0_013, h1_013, h3_013,
    h0_023, h2_023, h3_023, hn012, hn013, hn023,
    hτ012, hτ013, hτ023, h012013, h012023, h013023, ?_⟩
  intro σ hσK h0σ
  have hmemσ : σ ∈ incident := by simp [incident, hσK, h0σ]
  by_contra hcases
  push Not at hcases
  have hfive : [τ, ρ012, ρ013, ρ023, σ].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or,
      List.nodup_nil, and_true]
    aesop
  have hsub : [τ, ρ012, ρ013, ρ023, σ].toFinset ⊆ incident.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at hx ⊢
    simp at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hmemτ
    · exact hmem012
    · exact hmem013
    · exact hmem023
    · exact hmemσ
  have hcard := Finset.card_le_card hsub
  have hleft : [τ, ρ012, ρ013, ρ023, σ].toFinset.card = 5 := by
    simpa using List.toFinset_card_of_nodup hfive
  have hright : incident.toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup hincNodup, hincLength]
  rw [hleft, hright] at hcard
  omega

end Poincare
