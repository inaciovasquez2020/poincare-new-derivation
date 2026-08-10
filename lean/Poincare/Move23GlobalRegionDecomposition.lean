import Poincare.Move23UnchangedOverlap
import Poincare.TriangulationTopologicalGeometricCompactness

open Set

namespace Poincare

/-- Every canonical tetrahedral body is compact. -/
theorem triangulationTopologicalTetBody_isCompact (tau : Tet) :
    IsCompact (triangulationTopologicalTetBody tau) := by
  exact
    (Finset.finite_toSet tau.verts.toFinset).image
      triangulationTopologicalGeometricVertex |>.isCompact_convexHull ℝ

/-- The unchanged part of a Move23 site is a finite union of compact tetrahedral bodies. -/
theorem Move23Site.unchangedGeometricCarrier_isCompact
    (s : Move23Site) (K : Triangulation) :
    IsCompact (s.unchangedGeometricCarrier K) := by
  rw [Move23Site.unchangedGeometricCarrier]
  exact s.unchangedTets K |>.finite_toSet.isCompact_biUnion fun tau _ =>
    triangulationTopologicalTetBody_isCompact tau

theorem Move23Site.unchangedGeometricCarrier_isClosed
    (s : Move23Site) (K : Triangulation) :
    IsClosed (s.unchangedGeometricCarrier K) :=
  (s.unchangedGeometricCarrier_isCompact K).isClosed

theorem move23PiSourceLocalCarrier_isClosed (a b c d e : Nat) :
    IsClosed (move23PiSourceLocalCarrier a b c d e) :=
  (move23PiSourceLocalCarrier_isCompact a b c d e).isClosed

theorem move23PiTargetLocalCarrier_isClosed (a b c d e : Nat) :
    IsClosed (move23PiTargetLocalCarrier a b c d e) :=
  (move23PiTargetLocalCarrier_isCompact a b c d e).isClosed

/-- The original realization is the source move region together with the exact double-erasure tail. -/
theorem Move23Site.geometricComplex_space_eq_source_union_unchanged
    {K : Triangulation} (s : Move23Site) (hrealized : s.RealizedIn K) :
    (triangulationTopologicalGeometricComplex K).space =
      move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ∪
        s.unchangedGeometricCarrier K := by
  apply Set.Subset.antisymm
  · rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
    rintro p hp
    simp only [mem_iUnion] at hp
    obtain ⟨tau, htau, hpTau⟩ := hp
    change p ∈ triangulationTopologicalTetBody tau at hpTau
    by_cases hleft : SameTetVertices tau s.leftTet
    · left
      rw [triangulationTopologicalTetBody_eq_of_sameTetVertices hleft] at hpTau
      exact Or.inl (by simpa using hpTau)
    · by_cases hright : SameTetVertices tau s.rightTet
      · left
        rw [triangulationTopologicalTetBody_eq_of_sameTetVertices hright] at hpTau
        exact Or.inr (by simpa using hpTau)
      · right
        simp only [Move23Site.unchangedGeometricCarrier, mem_iUnion]
        refine ⟨tau, ?_, hpTau⟩
        exact mem_eraseFirstSameTet_of_mem_of_not_same
          (mem_eraseFirstSameTet_of_mem_of_not_same htau hleft) hright
  · apply union_subset
    · exact s.sourceLocalCarrier_subset_geometricCarrier hrealized
    · intro p hp
      simp only [Move23Site.unchangedGeometricCarrier, mem_iUnion] at hp
      obtain ⟨tau, htau, hpTau⟩ := hp
      apply triangulationTopologicalTetBody_subset_geometricCarrier _ hpTau
      exact mem_of_mem_eraseFirstSameTet (mem_of_mem_eraseFirstSameTet htau)

/-- The replacement realization is the target move region together with the same unchanged tail. -/
theorem Move23Site.replace_geometricComplex_space_eq_target_union_unchanged
    (s : Move23Site) (K : Triangulation) :
    (triangulationTopologicalGeometricComplex (s.replace K)).space =
      move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ∪
        s.unchangedGeometricCarrier K := by
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  change (⋃ (tau : Tet) (_ : tau ∈ (s.replace K).tets),
      triangulationTopologicalTetBody tau) = _
  rw [s.replace_tets_eq K, ← s.newTets_tetBody_union]
  ext p
  simp [Move23Site.unchangedGeometricCarrier]
  aesop

/-- For a legal site, both whole realizations share exactly the same unchanged region. -/
theorem ClosedTriangulationCore.move23Site_global_region_decomposition
    {K : Triangulation} (_hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    (triangulationTopologicalGeometricComplex K).space =
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ∪
          s.unchangedGeometricCarrier K ∧
      (triangulationTopologicalGeometricComplex (s.replace K)).space =
        move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ∪
          s.unchangedGeometricCarrier K := by
  exact ⟨s.geometricComplex_space_eq_source_union_unchanged hlegal.1,
    s.replace_geometricComplex_space_eq_target_union_unchanged K⟩

end Poincare
