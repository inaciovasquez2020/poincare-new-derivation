import Poincare.Move23CanonicalReverse

open Set

namespace Poincare

structure Move32Site where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat

def Move32Site.targetTet₀ (s : Move32Site) : Tet := ⟨s.a, s.b, s.d, s.e⟩
def Move32Site.targetTet₁ (s : Move32Site) : Tet := ⟨s.a, s.c, s.d, s.e⟩
def Move32Site.targetTet₂ (s : Move32Site) : Tet := ⟨s.b, s.c, s.d, s.e⟩
def Move32Site.sourceTet₀ (s : Move32Site) : Tet := ⟨s.a, s.b, s.c, s.d⟩
def Move32Site.sourceTet₁ (s : Move32Site) : Tet := ⟨s.a, s.b, s.c, s.e⟩

def Move32Site.RealizedIn (s : Move32Site) (K : Triangulation) : Prop :=
  (∃ tau ∈ K.tets, SameTetVertices tau s.targetTet₀) ∧
  (∃ tau ∈ K.tets, SameTetVertices tau s.targetTet₁) ∧
  (∃ tau ∈ K.tets, SameTetVertices tau s.targetTet₂)

def Move32Site.SharedEdgeExactlyThree (s : Move32Site) (K : Triangulation) : Prop :=
  (K.tets.filter (fun tau => s.d ∈ tau.verts ∧ s.e ∈ tau.verts)).length = 3

def Move32Site.SourceFaceAbsent (s : Move32Site) (K : Triangulation) : Prop :=
  ∀ tau ∈ K.tets, ¬ (s.a ∈ tau.verts ∧ s.b ∈ tau.verts ∧ s.c ∈ tau.verts)

def Move32Site.LegalIn (s : Move32Site) (K : Triangulation) : Prop :=
  s.RealizedIn K ∧ s.SharedEdgeExactlyThree K ∧ s.SourceFaceAbsent K

theorem ClosedTriangulationCore.move32Site_distinct {K : Triangulation}
    (hcore : ClosedTriangulationCore K) (s : Move32Site)
    (hrealized : s.RealizedIn K) : [s.a, s.b, s.c, s.d, s.e].Nodup := by
  rcases hrealized with ⟨⟨tau0, h0, hs0⟩, ⟨tau1, h1, hs1⟩, ⟨tau2, h2, hs2⟩⟩
  have hn0 := Tet.verts_nodup_of_sameTetVertices (hcore.1 tau0 h0) hs0
  have hn1 := Tet.verts_nodup_of_sameTetVertices (hcore.1 tau1 h1) hs1
  have hn2 := Tet.verts_nodup_of_sameTetVertices (hcore.1 tau2 h2) hs2
  simp [Move32Site.targetTet₀, Move32Site.targetTet₁, Move32Site.targetTet₂,
    Tet.verts] at hn0 hn1 hn2 ⊢
  aesop

def Move32Site.toMove23Site (s : Move32Site)
    (hfive : [s.a, s.b, s.c, s.d, s.e].Nodup) : Move23Site :=
  { a := s.a, b := s.b, c := s.c, d := s.d, e := s.e, distinct := hfive }

@[simp] theorem Move32Site.toMove23Site_leftTet (s : Move32Site) (hfive) :
    (s.toMove23Site hfive).leftTet = s.sourceTet₀ := rfl
@[simp] theorem Move32Site.toMove23Site_rightTet (s : Move32Site) (hfive) :
    (s.toMove23Site hfive).rightTet = s.sourceTet₁ := rfl
@[simp] theorem Move32Site.toMove23Site_newTet₀ (s : Move32Site) (hfive) :
    (s.toMove23Site hfive).newTet₀ = s.targetTet₀ := rfl
@[simp] theorem Move32Site.toMove23Site_newTet₁ (s : Move32Site) (hfive) :
    (s.toMove23Site hfive).newTet₁ = s.targetTet₁ := rfl
@[simp] theorem Move32Site.toMove23Site_newTet₂ (s : Move32Site) (hfive) :
    (s.toMove23Site hfive).newTet₂ = s.targetTet₂ := rfl

def Move32Site.unchangedTets (s : Move32Site) (K : Triangulation) : List Tet :=
  eraseFirstSameTet s.targetTet₂
    (eraseFirstSameTet s.targetTet₁ (eraseFirstSameTet s.targetTet₀ K.tets))

def Move32Site.replace (s : Move32Site) (K : Triangulation) : Triangulation :=
  { tets := s.sourceTet₀ :: s.sourceTet₁ :: s.unchangedTets K }

@[simp] theorem Move32Site.replace_tets_eq (s : Move32Site) (K : Triangulation) :
    (s.replace K).tets = s.sourceTet₀ :: s.sourceTet₁ :: s.unchangedTets K := rfl

theorem Move32Site.mem_original_of_mem_unchanged {s : Move32Site} {K : Triangulation}
    {tau : Tet} (h : tau ∈ s.unchangedTets K) : tau ∈ K.tets := by
  exact mem_of_mem_eraseFirstSameTet
    (mem_of_mem_eraseFirstSameTet (mem_of_mem_eraseFirstSameTet h))

noncomputable def Move32Site.unchangedGeometricCarrier
    (s : Move32Site) (K : Triangulation) : Set (Nat → ℝ) :=
  ⋃ (tau : Tet) (_ : tau ∈ s.unchangedTets K), triangulationTopologicalTetBody tau

theorem Move32Site.unchangedGeometricCarrier_isCompact (s : Move32Site)
    (K : Triangulation) : IsCompact (s.unchangedGeometricCarrier K) := by
  rw [Move32Site.unchangedGeometricCarrier]
  exact s.unchangedTets K |>.finite_toSet.isCompact_biUnion fun tau _ =>
    triangulationTopologicalTetBody_isCompact tau

theorem Move32Site.unchangedGeometricCarrier_isClosed (s : Move32Site)
    (K : Triangulation) : IsClosed (s.unchangedGeometricCarrier K) :=
  (s.unchangedGeometricCarrier_isCompact K).isClosed

def Move32Site.ofMove23Site (m : Move23Site) : Move32Site :=
  { a := m.a, b := m.b, c := m.c, d := m.d, e := m.e }

@[simp] theorem Move32Site.ofMove23Site_targetTet₀ (m : Move23Site) :
    (Move32Site.ofMove23Site m).targetTet₀ = m.newTet₀ := rfl
@[simp] theorem Move32Site.ofMove23Site_targetTet₁ (m : Move23Site) :
    (Move32Site.ofMove23Site m).targetTet₁ = m.newTet₁ := rfl
@[simp] theorem Move32Site.ofMove23Site_targetTet₂ (m : Move23Site) :
    (Move32Site.ofMove23Site m).targetTet₂ = m.newTet₂ := rfl
@[simp] theorem Move32Site.ofMove23Site_sourceTet₀ (m : Move23Site) :
    (Move32Site.ofMove23Site m).sourceTet₀ = m.leftTet := rfl
@[simp] theorem Move32Site.ofMove23Site_sourceTet₁ (m : Move23Site) :
    (Move32Site.ofMove23Site m).sourceTet₁ = m.rightTet := rfl

theorem Move32Site.ofMove23Site_unchangedTets_replace (m : Move23Site)
    (K : Triangulation) :
    (Move32Site.ofMove23Site m).unchangedTets (m.replace K) = m.unchangedTets K := by
  simp [Move32Site.unchangedTets, Move32Site.ofMove23Site, Move23Site.replace,
    Move23Site.unchangedTets, eraseFirstSameTet, sameTetVerticesBool,
    Move32Site.targetTet₀, Move32Site.targetTet₁, Move32Site.targetTet₂,
    Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts]

theorem Move32Site.ofMove23Site_replace_replace (m : Move23Site) (K : Triangulation) :
    (Move32Site.ofMove23Site m).replace (m.replace K) =
      m.reverseReplace (m.replace K) := by
  rw [m.reverseReplace_replace_eq_canonicalPredecessor K]
  simp [Move32Site.replace, Move23Site.canonicalPredecessor,
    Move32Site.ofMove23Site_unchangedTets_replace]

@[simp] theorem Move32Site.targetTet₀_tetBody (s : Move32Site) :
    triangulationTopologicalTetBody s.targetTet₀ =
      move23PiTetrahedronBody ![s.a, s.b, s.d, s.e] := by
  exact triangulationTopologicalTetBody_mk_eq_piBody _ _ _ _
@[simp] theorem Move32Site.targetTet₁_tetBody (s : Move32Site) :
    triangulationTopologicalTetBody s.targetTet₁ =
      move23PiTetrahedronBody ![s.a, s.c, s.d, s.e] := by
  exact triangulationTopologicalTetBody_mk_eq_piBody _ _ _ _
@[simp] theorem Move32Site.targetTet₂_tetBody (s : Move32Site) :
    triangulationTopologicalTetBody s.targetTet₂ =
      move23PiTetrahedronBody ![s.b, s.c, s.d, s.e] := by
  exact triangulationTopologicalTetBody_mk_eq_piBody _ _ _ _
@[simp] theorem Move32Site.sourceTet₀_tetBody (s : Move32Site) :
    triangulationTopologicalTetBody s.sourceTet₀ =
      move23PiTetrahedronBody ![s.a, s.b, s.c, s.d] := by
  exact triangulationTopologicalTetBody_mk_eq_piBody _ _ _ _
@[simp] theorem Move32Site.sourceTet₁_tetBody (s : Move32Site) :
    triangulationTopologicalTetBody s.sourceTet₁ =
      move23PiTetrahedronBody ![s.a, s.b, s.c, s.e] := by
  exact triangulationTopologicalTetBody_mk_eq_piBody _ _ _ _

theorem Move32Site.exists_actual_target_region {K : Triangulation} (s : Move32Site)
    (hrealized : s.RealizedIn K) :
    ∃ tau0 tau1 tau2 : Tet, tau0 ∈ K.tets ∧ tau1 ∈ K.tets ∧ tau2 ∈ K.tets ∧
      SameTetVertices tau0 s.targetTet₀ ∧ SameTetVertices tau1 s.targetTet₁ ∧
      SameTetVertices tau2 s.targetTet₂ ∧
      triangulationTopologicalTetBody tau0 ∪ triangulationTopologicalTetBody tau1 ∪
        triangulationTopologicalTetBody tau2 = move23PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
  rcases hrealized with ⟨⟨tau0, h0, hs0⟩, ⟨tau1, h1, hs1⟩, ⟨tau2, h2, hs2⟩⟩
  refine ⟨tau0, tau1, tau2, h0, h1, h2, hs0, hs1, hs2, ?_⟩
  rw [triangulationTopologicalTetBody_eq_of_sameTetVertices hs0,
    triangulationTopologicalTetBody_eq_of_sameTetVertices hs1,
    triangulationTopologicalTetBody_eq_of_sameTetVertices hs2]
  simp [move23PiTargetLocalCarrier, move23PiABDE, move23PiACDE, move23PiBCDE]

theorem Move32Site.targetLocalCarrier_subset_geometricCarrier {K : Triangulation}
    (s : Move32Site) (hrealized : s.RealizedIn K) :
    move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ⊆
      (triangulationTopologicalGeometricComplex K).space := by
  obtain ⟨tau0, tau1, tau2, h0, h1, h2, _, _, _, heq⟩ :=
    s.exists_actual_target_region hrealized
  rw [← heq]
  exact union_subset (union_subset
    (triangulationTopologicalTetBody_subset_geometricCarrier h0)
    (triangulationTopologicalTetBody_subset_geometricCarrier h1))
    (triangulationTopologicalTetBody_subset_geometricCarrier h2)

theorem Move32Site.sourceTets_mem_replace (s : Move32Site) (K : Triangulation) :
    s.sourceTet₀ ∈ (s.replace K).tets ∧ s.sourceTet₁ ∈ (s.replace K).tets := by simp

theorem Move32Site.sourceLocalCarrier_subset_replace_geometricCarrier
    (s : Move32Site) (K : Triangulation) :
    move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ⊆
      (triangulationTopologicalGeometricComplex (s.replace K)).space := by
  rw [move23PiSourceLocalCarrier]
  simp only [move23PiABCD, move23PiABCE]
  rw [← s.sourceTet₀_tetBody, ← s.sourceTet₁_tetBody]
  exact union_subset
    (triangulationTopologicalTetBody_subset_geometricCarrier (s.sourceTets_mem_replace K).1)
    (triangulationTopologicalTetBody_subset_geometricCarrier (s.sourceTets_mem_replace K).2)

theorem Move32Site.geometricComplex_space_eq_target_union_unchanged {K : Triangulation}
    (s : Move32Site) (hrealized : s.RealizedIn K) :
    (triangulationTopologicalGeometricComplex K).space =
      move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ∪ s.unchangedGeometricCarrier K := by
  apply Set.Subset.antisymm
  · rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
    rintro p hp
    simp only [mem_iUnion] at hp
    obtain ⟨tau, htau, hpTau⟩ := hp
    change p ∈ triangulationTopologicalTetBody tau at hpTau
    by_cases h0 : SameTetVertices tau s.targetTet₀
    · left; rw [triangulationTopologicalTetBody_eq_of_sameTetVertices h0] at hpTau
      exact Or.inl (Or.inl (by simpa using hpTau))
    · by_cases h1 : SameTetVertices tau s.targetTet₁
      · left; rw [triangulationTopologicalTetBody_eq_of_sameTetVertices h1] at hpTau
        exact Or.inl (Or.inr (by simpa using hpTau))
      · by_cases h2 : SameTetVertices tau s.targetTet₂
        · left; rw [triangulationTopologicalTetBody_eq_of_sameTetVertices h2] at hpTau
          exact Or.inr (by simpa using hpTau)
        · right
          simp only [Move32Site.unchangedGeometricCarrier, mem_iUnion]
          exact ⟨tau, mem_eraseFirstSameTet_of_mem_of_not_same
            (mem_eraseFirstSameTet_of_mem_of_not_same
              (mem_eraseFirstSameTet_of_mem_of_not_same htau h0) h1) h2, hpTau⟩
  · apply union_subset
    · exact s.targetLocalCarrier_subset_geometricCarrier hrealized
    · rintro p hp
      simp only [Move32Site.unchangedGeometricCarrier, mem_iUnion] at hp
      obtain ⟨tau, htau, hpTau⟩ := hp
      exact triangulationTopologicalTetBody_subset_geometricCarrier
        (Move32Site.mem_original_of_mem_unchanged htau) hpTau

theorem Move32Site.replace_geometricComplex_space_eq_source_union_unchanged
    (s : Move32Site) (K : Triangulation) :
    (triangulationTopologicalGeometricComplex (s.replace K)).space =
      move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ∪ s.unchangedGeometricCarrier K := by
  rw [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion]
  change (⋃ (tau : Tet) (_ : tau ∈ (s.replace K).tets),
    triangulationTopologicalTetBody tau) = _
  rw [s.replace_tets_eq K, move23PiSourceLocalCarrier]
  simp only [move23PiABCD, move23PiABCE]
  rw [
    ← s.sourceTet₀_tetBody, ← s.sourceTet₁_tetBody]
  ext p
  simp only [Move32Site.unchangedGeometricCarrier, mem_iUnion, mem_union,
    List.mem_cons]
  aesop

theorem ClosedTriangulationCore.move32Site_global_region_decomposition
    {K : Triangulation} (_hcore : ClosedTriangulationCore K) (s : Move32Site)
    (hlegal : s.LegalIn K) :
    (triangulationTopologicalGeometricComplex K).space =
        move23PiTargetLocalCarrier s.a s.b s.c s.d s.e ∪ s.unchangedGeometricCarrier K ∧
      (triangulationTopologicalGeometricComplex (s.replace K)).space =
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e ∪ s.unchangedGeometricCarrier K := by
  exact ⟨s.geometricComplex_space_eq_target_union_unchanged hlegal.1,
    s.replace_geometricComplex_space_eq_source_union_unchanged K⟩

end Poincare
