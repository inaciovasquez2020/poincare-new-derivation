import Poincare.PositionStellarFaceCount

namespace Poincare

/-- Closed-core validity depends only on the multiset of tetrahedron records,
not their list order. The pairwise condition uses symmetry of distinct vertex
sets; the incidence condition uses exact filtered multiplicity preservation. -/
theorem ClosedTriangulationCore.of_tets_perm
    {K L : Triangulation} (hcore : ClosedTriangulationCore K)
    (hperm : K.tets.Perm L.tets) : ClosedTriangulationCore L := by
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    exact hcore.1 τ ((hperm.mem_iff).2 hτ)
  · exact hcore.2.1.perm hperm (by
      intro τ σ hnot hsame
      exact hnot (sameTetVertices_symm hsame))
  · intro a b c habc hrep
    have hrepK : ∃ τ ∈ K.tets,
        a ∈ τ.verts ∧ b ∈ τ.verts ∧ c ∈ τ.verts := by
      obtain ⟨τ, hτ, hp⟩ := hrep
      exact ⟨τ, (hperm.mem_iff).2 hτ, hp⟩
    have hcounts := (hperm.filter (fun τ : Tet =>
      decide (a ∈ τ.verts ∧ b ∈ τ.verts ∧ c ∈ τ.verts))).length_eq
    exact hcounts.symm.trans (hcore.2.2 a b c habc hrepK)

/-- Arbitrary-position fresh 1→4 insertion preserves closed-core validity,
as a literal ordered-list result. This does not construct a
`CertifiedPachnerStep`: that relation's inverse constructor still places
the selected target tetrahedron at the head. -/
theorem Move41Site.insertFreshAt_closedCore
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hcore : ClosedTriangulationCore K)
    (hfresh : s.e ∉ vertexSupport K) :
    ClosedTriangulationCore
      (s.insertFreshAt K before after hsource hfresh) := by
  have hpermSource : K.tets.Perm
      (s.targetTet :: (before ++ after)) := by
    rw [hsource]
    exact List.perm_middle
  have hheadCore : ClosedTriangulationCore
      ({ tets := s.targetTet :: (before ++ after) } : Triangulation) :=
    hcore.of_tets_perm hpermSource
  have hfreshRest : ∀ τ ∈ before ++ after, s.e ∉ τ.verts := by
    intro τ hτ hcenter
    apply hfresh
    apply (mem_vertexSupport_iff K s.e).2
    change s.e ∈ K.tets.flatMap Tet.verts
    apply List.mem_flatMap.mpr
    refine ⟨τ, ?_, hcenter⟩
    rw [hsource]
    rcases List.mem_append.mp hτ with hb | ha
    · exact List.mem_append.mpr (Or.inl hb)
    · exact List.mem_append.mpr
        (Or.inr (List.mem_cons_of_mem _ ha))
  have hstellar : ClosedTriangulationCore
      (s.headStellar (before ++ after)) :=
    s.headStellar_closedCore (before ++ after) hheadCore hfreshRest
  have hpermTarget :
      (s.insertFreshAt K before after hsource hfresh).tets.Perm
        (s.headStellar (before ++ after)).tets := by
    change (before ++ s.sourceTets ++ after).Perm
      (s.sourceTets ++ (before ++ after))
    simpa [List.append_assoc] using
      (List.perm_append_comm_assoc before s.sourceTets after)
  exact hstellar.of_tets_perm hpermTarget.symm

end Poincare
