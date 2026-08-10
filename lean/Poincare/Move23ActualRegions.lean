import Poincare.Move23PiRealizationChange
import Poincare.TriangulationTopologicalGeometricDecomposition

open Set

namespace Poincare

/-- The filled geometric body of a tetrahedron in the canonical Pi-space realization. -/
noncomputable def triangulationTopologicalTetBody (tau : Tet) : Set (Nat → ℝ) :=
  convexHull ℝ
    (triangulationTopologicalGeometricVertex ''
      (↑tau.verts.toFinset : Set Nat))

/-- A tetrahedral body depends only on the represented vertex set. -/
theorem triangulationTopologicalTetBody_eq_of_sameTetVertices
    {tau rho : Tet} (h : SameTetVertices tau rho) :
    triangulationTopologicalTetBody tau =
      triangulationTopologicalTetBody rho := by
  have hverts : tau.verts.toFinset = rho.verts.toFinset := by
    ext v
    simpa using h v
  simp [triangulationTopologicalTetBody, hverts]

theorem triangulationTopologicalTetBody_mk_eq_piBody (a b c d : Nat) :
    triangulationTopologicalTetBody ⟨a, b, c, d⟩ =
      move23PiTetrahedronBody ![a, b, c, d] := by
  unfold triangulationTopologicalTetBody move23PiTetrahedronBody
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, Finset.mem_coe, List.mem_toFinset,
    Tet.verts, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨v, rfl | rfl | rfl | rfl, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨a, by simp, rfl⟩
    · exact ⟨b, by simp, rfl⟩
    · exact ⟨c, by simp, rfl⟩
    · exact ⟨d, by simp, rfl⟩

@[simp] theorem Move23Site.leftTet_tetBody (s : Move23Site) :
    triangulationTopologicalTetBody s.leftTet =
      move23PiTetrahedronBody (move23PiABCD s.a s.b s.c s.d s.e) := by
  simpa [Move23Site.leftTet, move23PiABCD] using
    triangulationTopologicalTetBody_mk_eq_piBody s.a s.b s.c s.d

@[simp] theorem Move23Site.rightTet_tetBody (s : Move23Site) :
    triangulationTopologicalTetBody s.rightTet =
      move23PiTetrahedronBody (move23PiABCE s.a s.b s.c s.d s.e) := by
  simpa [Move23Site.rightTet, move23PiABCE] using
    triangulationTopologicalTetBody_mk_eq_piBody s.a s.b s.c s.e

@[simp] theorem Move23Site.newTet₀_tetBody (s : Move23Site) :
    triangulationTopologicalTetBody s.newTet₀ =
      move23PiTetrahedronBody (move23PiABDE s.a s.b s.c s.d s.e) := by
  simpa [Move23Site.newTet₀, move23PiABDE] using
    triangulationTopologicalTetBody_mk_eq_piBody s.a s.b s.d s.e

@[simp] theorem Move23Site.newTet₁_tetBody (s : Move23Site) :
    triangulationTopologicalTetBody s.newTet₁ =
      move23PiTetrahedronBody (move23PiACDE s.a s.b s.c s.d s.e) := by
  simpa [Move23Site.newTet₁, move23PiACDE] using
    triangulationTopologicalTetBody_mk_eq_piBody s.a s.c s.d s.e

@[simp] theorem Move23Site.newTet₂_tetBody (s : Move23Site) :
    triangulationTopologicalTetBody s.newTet₂ =
      move23PiTetrahedronBody (move23PiBCDE s.a s.b s.c s.d s.e) := by
  simpa [Move23Site.newTet₂, move23PiBCDE] using
    triangulationTopologicalTetBody_mk_eq_piBody s.b s.c s.d s.e

theorem Move23Site.exists_actual_source_region
    {K : Triangulation} (s : Move23Site) (hrealized : s.RealizedIn K) :
    ∃ tauL tauR : Tet,
      tauL ∈ K.tets ∧ tauR ∈ K.tets ∧
      SameTetVertices tauL s.leftTet ∧
      SameTetVertices tauR s.rightTet ∧
      triangulationTopologicalTetBody tauL ∪
          triangulationTopologicalTetBody tauR =
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e := by
  rcases hrealized with ⟨⟨tauL, hL, hsL⟩, ⟨tauR, hR, hsR⟩⟩
  refine ⟨tauL, tauR, hL, hR, hsL, hsR, ?_⟩
  rw [triangulationTopologicalTetBody_eq_of_sameTetVertices hsL,
    triangulationTopologicalTetBody_eq_of_sameTetVertices hsR]
  simp [move23PiSourceLocalCarrier]

theorem triangulationTopologicalTetBody_subset_geometricCarrier
    {K : Triangulation} {tau : Tet} (htau : tau ∈ K.tets) :
    triangulationTopologicalTetBody tau ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  intro x hx
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  simp only [mem_iUnion]
  exact ⟨tau, htau, hx⟩

theorem Move23Site.sourceLocalCarrier_subset_geometricCarrier
    {K : Triangulation} (s : Move23Site) (hrealized : s.RealizedIn K) :
    move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  obtain ⟨tauL, tauR, hL, hR, _, _, heq⟩ :=
    s.exists_actual_source_region hrealized
  rw [← heq]
  exact union_subset
    (triangulationTopologicalTetBody_subset_geometricCarrier hL)
    (triangulationTopologicalTetBody_subset_geometricCarrier hR)

theorem Move23Site.newTets_mem_replace (s : Move23Site) (K : Triangulation) :
    s.newTet₀ ∈ (s.replace K).tets ∧
    s.newTet₁ ∈ (s.replace K).tets ∧
    s.newTet₂ ∈ (s.replace K).tets := by
  simp [Move23Site.replace]

theorem Move23Site.newTets_tetBody_union (s : Move23Site) :
    triangulationTopologicalTetBody s.newTet₀ ∪
        triangulationTopologicalTetBody s.newTet₁ ∪
        triangulationTopologicalTetBody s.newTet₂ =
      move23PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
  simp [move23PiTargetLocalCarrier]

theorem Move23Site.targetLocalCarrier_subset_replace_geometricCarrier
    (s : Move23Site) (K : Triangulation) :
    move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ⊆
      (triangulationTopologicalGeometricComplex (s.replace K)).space := by
  rw [← s.newTets_tetBody_union]
  rcases s.newTets_mem_replace K with ⟨h0, h1, h2⟩
  exact union_subset
    (union_subset
      (triangulationTopologicalTetBody_subset_geometricCarrier h0)
      (triangulationTopologicalTetBody_subset_geometricCarrier h1))
    (triangulationTopologicalTetBody_subset_geometricCarrier h2)

theorem ClosedTriangulationCore.move23Site_actual_region_pair
    {K : Triangulation} (_hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ⊆
        (triangulationTopologicalGeometricComplex K).space ∧
      move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ⊆
        (triangulationTopologicalGeometricComplex (s.replace K)).space := by
  exact ⟨s.sourceLocalCarrier_subset_geometricCarrier hlegal.1,
    s.targetLocalCarrier_subset_replace_geometricCarrier K⟩

end Poincare
