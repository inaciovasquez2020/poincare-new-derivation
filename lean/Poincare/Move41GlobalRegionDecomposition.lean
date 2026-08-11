import Poincare.Move41LocalCarrier
import Poincare.Move23ActualRegions
import Poincare.TriangulationTopologicalVertexStarNeighborhood

open Set

namespace Poincare

/-- The geometric carrier of the tetrahedra untouched by a `4 → 1` move. -/
noncomputable def Move41Site.unchangedGeometricCarrier
    (s : Move41Site) (K : Triangulation) : Set (Nat → ℝ) :=
  ⋃ τ ∈ s.unchangedTets K, triangulationTopologicalTetBody τ

/-- No tetrahedron surviving a legal `4 → 1` erasure contains the removed
center.  This is the combinatorial boundary fact needed to glue the radial
local map to the identity on the unchanged carrier. -/
theorem ClosedTriangulationCore.move41Site_unchangedTet_center_not_mem
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) {tau : Tet}
    (htau : tau ∈ s.unchangedTets K) :
    s.e ∉ tau.verts := by
  intro he
  have htauK : tau ∈ K.tets :=
    mem_of_mem_eraseFirstSameTet
      (mem_of_mem_eraseFirstSameTet
        (mem_of_mem_eraseFirstSameTet
          (mem_of_mem_eraseFirstSameTet htau)))
  rcases (Move41Site.mem_source_iff_of_center_mem hlegal htauK).1 he with
    ⟨source, hsource, hsame⟩
  have sourceUnique (rho : Tet) (hrho : rho ∈ s.sourceTets) :
      ∃! sigma, sigma ∈ K.tets ∧ SameTetVertices sigma rho := by
    have hlen := hlegal.sourceOccursExactlyOnce rho hrho
    have hex : ∃ sigma ∈ K.tets, SameTetVertices sigma rho := by
      have hne : K.tets.filter
          (fun sigma => sameTetVerticesBool sigma rho) ≠ [] := by
        intro hempty
        simp [hempty] at hlen
      rcases List.exists_mem_of_ne_nil _ hne with ⟨sigma, hsigma⟩
      exact ⟨sigma, by simpa [sameTetVerticesBool_eq_true_iff] using hsigma⟩
    exact hcore.existsUnique_sameTetVertices hex
  have hnK : K.tets.Nodup := hcore.2.1.imp (fun hnot heq =>
    hnot (by subst heq; exact sameTetVertices_refl _))
  have hp := hlegal.sourcePairwiseDistinct
  simp [Move41Site.sourceTets] at hp hsource
  rcases hsource with rfl | rfl | rfl | rfl
  · exact (not_same_of_mem_eraseFirstSameTet_of_unique hnK
      (sourceUnique s.sourceTet₀ (by simp [Move41Site.sourceTets]))
      (mem_of_mem_eraseFirstSameTet
        (mem_of_mem_eraseFirstSameTet
          (mem_of_mem_eraseFirstSameTet htau)))) hsame
  · have hu := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
        (sourceUnique s.sourceTet₁ (by simp [Move41Site.sourceTets]))
        (fun h => hp.1.1 (sameTetVertices_symm h))
    exact (not_same_of_mem_eraseFirstSameTet_of_unique
      (hnK.sublist (eraseFirstSameTet_sublist _ _)) hu
      (mem_of_mem_eraseFirstSameTet (mem_of_mem_eraseFirstSameTet htau))) hsame
  · have hu := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
        (sourceUnique s.sourceTet₂ (by simp [Move41Site.sourceTets]))
        (fun h => hp.1.2.1 (sameTetVertices_symm h))
    have hu' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu
      (fun h => hp.2.1.1 (sameTetVertices_symm h))
    exact (not_same_of_mem_eraseFirstSameTet_of_unique
      ((hnK.sublist (eraseFirstSameTet_sublist _ _)).sublist
        (eraseFirstSameTet_sublist _ _)) hu'
      (mem_of_mem_eraseFirstSameTet htau)) hsame
  · have hu := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
        (sourceUnique s.sourceTet₃ (by simp [Move41Site.sourceTets]))
        (fun h => hp.1.2.2 (sameTetVertices_symm h))
    have hu' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu
      (fun h => hp.2.1.2 (sameTetVertices_symm h))
    have hu'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu'
      (fun h => hp.2.2 (sameTetVertices_symm h))
    exact (not_same_of_mem_eraseFirstSameTet_of_unique
      (((hnK.sublist (eraseFirstSameTet_sublist _ _)).sublist
        (eraseFirstSameTet_sublist _ _)).sublist
          (eraseFirstSameTet_sublist _ _)) hu'' htau) hsame

/-- The unchanged tail of a `4 → 1` move is closed, being a finite union of
compact tetrahedral bodies. -/
theorem Move41Site.unchangedGeometricCarrier_isClosed
    (s : Move41Site) (K : Triangulation) :
    IsClosed (s.unchangedGeometricCarrier K) := by
  apply IsCompact.isClosed
  rw [Move41Site.unchangedGeometricCarrier]
  exact s.unchangedTets K |>.finite_toSet.isCompact_biUnion fun tau _ =>
    triangulationTopologicalTetBody_isCompact tau

/-- A legal `4 → 1` replacement changes exactly its explicit local carrier;
the source and target realizations have the same unchanged geometric tail. -/
theorem ClosedTriangulationCore.move41Site_global_region_decomposition
    {K : Triangulation} (_hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    (triangulationTopologicalGeometricComplex K).space =
        move41PiSourceLocalCarrier s.a s.b s.c s.d s.e ∪
          s.unchangedGeometricCarrier K ∧
      (triangulationTopologicalGeometricComplex (s.replace K)).space =
        move41PiTargetLocalCarrier s.a s.b s.c s.d s.e ∪
          s.unchangedGeometricCarrier K := by
  have sourceExists (source : Tet) (hsource : source ∈ s.sourceTets) :
      ∃ ρ ∈ K.tets, SameTetVertices ρ source := by
    have hlength := hlegal.sourceOccursExactlyOnce source hsource
    have hne : K.tets.filter (fun σ => sameTetVerticesBool σ source) ≠ [] := by
      intro hempty
      simp [hempty] at hlength
    rcases List.exists_mem_of_ne_nil _ hne with ⟨ρ, hρ⟩
    have hρ' : ρ ∈ K.tets ∧ SameTetVertices ρ source := by
      simpa [sameTetVerticesBool_eq_true_iff] using hρ
    exact ⟨ρ, hρ'.1, hρ'.2⟩
  constructor
  · apply Set.Subset.antisymm
    · rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
      rintro p hp
      simp only [mem_iUnion] at hp
      obtain ⟨τ, hτ, hpτ⟩ := hp
      change p ∈ triangulationTopologicalTetBody τ at hpτ
      by_cases heτ : s.e ∈ τ.verts
      · left
        rcases (Move41Site.mem_source_iff_of_center_mem hlegal hτ).1 heτ with
          ⟨source, hsource, hsame⟩
        rw [triangulationTopologicalTetBody_eq_of_sameTetVertices hsame] at hpτ
        simp [Move41Site.sourceTets] at hsource
        rcases hsource with rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inl (Or.inl (by
            rw [triangulationTopologicalTetBody_mk_eq_piBody] at hpτ
            simpa [move23PiABCE] using hpτ)))
        · exact Or.inl (Or.inl (Or.inr (by
            rw [triangulationTopologicalTetBody_mk_eq_piBody] at hpτ
            simpa [move23PiABDE] using hpτ)))
        · exact Or.inl (Or.inr (by
            rw [triangulationTopologicalTetBody_mk_eq_piBody] at hpτ
            simpa [move23PiACDE] using hpτ))
        · exact Or.inr (by
            rw [triangulationTopologicalTetBody_mk_eq_piBody] at hpτ
            simpa [move23PiBCDE] using hpτ)
      · right
        simp only [Move41Site.unchangedGeometricCarrier, mem_iUnion]
        refine ⟨τ, ?_, hpτ⟩
        have hnotSource : ∀ source ∈ s.sourceTets,
            ¬ SameTetVertices τ source := by
          intro source hsource hsame
          apply heτ
          apply (hsame s.e).2
          simp [Move41Site.sourceTets] at hsource
          rcases hsource with rfl | rfl | rfl | rfl <;>
            simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
              Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]
        exact mem_eraseFirstSameTet_of_mem_of_not_same
          (mem_eraseFirstSameTet_of_mem_of_not_same
            (mem_eraseFirstSameTet_of_mem_of_not_same
              (mem_eraseFirstSameTet_of_mem_of_not_same hτ
                (hnotSource s.sourceTet₀ (by simp [Move41Site.sourceTets])))
              (hnotSource s.sourceTet₁ (by simp [Move41Site.sourceTets])))
            (hnotSource s.sourceTet₂ (by simp [Move41Site.sourceTets])))
          (hnotSource s.sourceTet₃ (by simp [Move41Site.sourceTets]))
    · apply union_subset
      · intro p hp
        rw [move41PiSourceLocalCarrier] at hp
        change
          ((p ∈ move23PiTetrahedronBody (move23PiABCE s.a s.b s.c s.d s.e) ∨
              p ∈ move23PiTetrahedronBody (move23PiABDE s.a s.b s.c s.d s.e)) ∨
            p ∈ move23PiTetrahedronBody (move23PiACDE s.a s.b s.c s.d s.e)) ∨
          p ∈ move23PiTetrahedronBody (move23PiBCDE s.a s.b s.c s.d s.e) at hp
        rcases hp with ((hp | hp) | hp) | hp
        · rcases sourceExists s.sourceTet₀ (by simp [Move41Site.sourceTets]) with
          ⟨ρ, hρ, hsame⟩
          apply triangulationTopologicalTetBody_subset_geometricCarrier hρ
          rw [triangulationTopologicalTetBody_eq_of_sameTetVertices hsame,
            triangulationTopologicalTetBody_mk_eq_piBody]
          simpa [move23PiABCE] using hp
        · rcases sourceExists s.sourceTet₁ (by simp [Move41Site.sourceTets]) with
          ⟨ρ, hρ, hsame⟩
          apply triangulationTopologicalTetBody_subset_geometricCarrier hρ
          rw [triangulationTopologicalTetBody_eq_of_sameTetVertices hsame,
            triangulationTopologicalTetBody_mk_eq_piBody]
          simpa [move23PiABDE] using hp
        · rcases sourceExists s.sourceTet₂ (by simp [Move41Site.sourceTets]) with
          ⟨ρ, hρ, hsame⟩
          apply triangulationTopologicalTetBody_subset_geometricCarrier hρ
          rw [triangulationTopologicalTetBody_eq_of_sameTetVertices hsame,
            triangulationTopologicalTetBody_mk_eq_piBody]
          simpa [move23PiACDE] using hp
        · rcases sourceExists s.sourceTet₃ (by simp [Move41Site.sourceTets]) with
          ⟨ρ, hρ, hsame⟩
          apply triangulationTopologicalTetBody_subset_geometricCarrier hρ
          rw [triangulationTopologicalTetBody_eq_of_sameTetVertices hsame,
            triangulationTopologicalTetBody_mk_eq_piBody]
          simpa [move23PiBCDE] using hp
      · intro p hp
        simp only [Move41Site.unchangedGeometricCarrier, mem_iUnion] at hp
        obtain ⟨τ, hτ, hpτ⟩ := hp
        exact triangulationTopologicalTetBody_subset_geometricCarrier
          (mem_of_mem_eraseFirstSameTet
            (mem_of_mem_eraseFirstSameTet
              (mem_of_mem_eraseFirstSameTet
                (mem_of_mem_eraseFirstSameTet hτ)))) hpτ
  · rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
    change (⋃ (τ : Tet) (_ : τ ∈ (s.replace K).tets),
      triangulationTopologicalTetBody τ) = _
    ext p
    rw [move41PiTargetLocalCarrier]
    simp only [move23PiABCD]
    rw [
      ← triangulationTopologicalTetBody_mk_eq_piBody s.a s.b s.c s.d]
    simp [Move41Site.replace, Move41Site.unchangedGeometricCarrier,
      Move41Site.targetTet]

/-- On the overlap with the unchanged carrier, the explicit `4 → 1` local
map agrees with the identity.  This is the compatibility datum for the
closed-cover gluing construction of the global carrier homeomorphism. -/
theorem ClosedTriangulationCore.move41Site_radialMap_eq_self_of_mem_unchanged
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) {p : Nat → ℝ}
    (hpS : p ∈ move41PiSourceLocalCarrier s.a s.b s.c s.d s.e)
    (hpU : p ∈ s.unchangedGeometricCarrier K) :
    move41PiRadialMap s.a s.b s.c s.d s.e p = p := by
  apply move41PiRadialMap_eq_self_of_center_eq_zero hpS
  simp only [Move41Site.unchangedGeometricCarrier, mem_iUnion] at hpU
  obtain ⟨tau, htau, hpTau⟩ := hpU
  exact triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem tau s.e
    (hcore.move41Site_unchangedTet_center_not_mem s hlegal htau) hpTau

end Poincare
