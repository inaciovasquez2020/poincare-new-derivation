import Poincare.Move23BipyramidGeometry
import Poincare.Move23SimpleBistellarData
import Poincare.TriangulationTopologicalGeometricComplex

open Set

namespace Poincare

/-- The five raw Move23 labels, in bipyramid order. -/
def move23Label (a b c d e : Nat) : Fin 5 → Nat :=
  [a, b, c, d, e].get

@[simp] theorem move23Label_zero (a b c d e : Nat) : move23Label a b c d e 0 = a := rfl
@[simp] theorem move23Label_one (a b c d e : Nat) : move23Label a b c d e 1 = b := rfl
@[simp] theorem move23Label_two (a b c d e : Nat) : move23Label a b c d e 2 = c := rfl
@[simp] theorem move23Label_three (a b c d e : Nat) : move23Label a b c d e 3 = d := rfl
@[simp] theorem move23Label_four (a b c d e : Nat) : move23Label a b c d e 4 = e := rfl

theorem move23Label_injective {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) : Function.Injective (move23Label a b c d e) :=
  h.injective_get

/-- The five vertices of the standard triangular bipyramid. -/
def move23BipyramidVertex : Fin 5 → Move23BipyramidAmbient :=
  ![move23BipyramidA, move23BipyramidB, move23BipyramidC,
    move23BipyramidD, move23BipyramidE]

/-- Finite-coordinate realization map from the actual Pi-space labels. -/
noncomputable def move23PiLinearMap (a b c d e : Nat) :
    (Nat → ℝ) →ₗ[ℝ] Move23BipyramidAmbient where
  toFun p := ∑ i : Fin 5, p (move23Label a b c d e i) • move23BipyramidVertex i
  map_add' p q := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r p := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

@[simp] theorem move23PiLinearMap_basisVertex
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) (i : Fin 5) :
    move23PiLinearMap a b c d e
        (triangulationTopologicalGeometricVertex (move23Label a b c d e i)) =
      move23BipyramidVertex i := by
  classical
  unfold move23PiLinearMap
  change (∑ j : Fin 5,
    triangulationTopologicalGeometricVertex (move23Label a b c d e i)
        (move23Label a b c d e j) • move23BipyramidVertex j) = _
  rw [Fintype.sum_eq_single i]
  · simp [triangulationTopologicalGeometricVertex]
  · intro j hji
    have hlabel : move23Label a b c d e j ≠ move23Label a b c d e i :=
      fun heq => hji ((move23Label_injective h) heq)
    simp [triangulationTopologicalGeometricVertex, hlabel]

theorem continuous_move23PiLinearMap (a b c d e : Nat) :
    Continuous (move23PiLinearMap a b c d e) := by
  unfold move23PiLinearMap
  change Continuous (fun p : Nat → ℝ ↦ ∑ i : Fin 5,
    p (move23Label a b c d e i) • move23BipyramidVertex i)
  apply continuous_finset_sum Finset.univ
  intro i _
  exact (continuous_apply (move23Label a b c d e i) :
    Continuous (fun p : Nat → ℝ ↦ p (move23Label a b c d e i))).smul continuous_const

def move23PiABCD (a b c d e : Nat) : Fin 4 → Nat := ![a, b, c, d]
def move23PiABCE (a b c d e : Nat) : Fin 4 → Nat := ![a, b, c, e]
def move23PiABDE (a b c d e : Nat) : Fin 4 → Nat := ![a, b, d, e]
def move23PiACDE (a b c d e : Nat) : Fin 4 → Nat := ![a, c, d, e]
def move23PiBCDE (a b c d e : Nat) : Fin 4 → Nat := ![b, c, d, e]

noncomputable def move23PiTetrahedronBody (v : Fin 4 → Nat) : Set (Nat → ℝ) :=
  convexHull ℝ (Set.range (fun i => triangulationTopologicalGeometricVertex (v i)))

noncomputable def move23PiSourceLocalCarrier (a b c d e : Nat) : Set (Nat → ℝ) :=
  move23PiTetrahedronBody (move23PiABCD a b c d e) ∪
    move23PiTetrahedronBody (move23PiABCE a b c d e)

noncomputable def move23PiTargetLocalCarrier (a b c d e : Nat) : Set (Nat → ℝ) :=
  move23PiTetrahedronBody (move23PiABDE a b c d e) ∪
    move23PiTetrahedronBody (move23PiACDE a b c d e) ∪
      move23PiTetrahedronBody (move23PiBCDE a b c d e)

private theorem move23PiLinearMap_image_face
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    (v : Fin 4 → Nat) (w : Fin 4 → Move23BipyramidAmbient)
    (hv : ∀ i, ∃ j, v i = move23Label a b c d e j ∧ w i = move23BipyramidVertex j) :
    move23PiLinearMap a b c d e '' move23PiTetrahedronBody v =
      move23TetrahedronBody w := by
  rw [move23PiTetrahedronBody, move23TetrahedronBody, LinearMap.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    obtain ⟨j, hvj, hwj⟩ := hv i
    refine ⟨i, ?_⟩
    change w i = move23PiLinearMap a b c d e
      (triangulationTopologicalGeometricVertex (v i))
    rw [hvj, move23PiLinearMap_basisVertex h, hwj]
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hvj, hwj⟩ := hv i
    refine ⟨triangulationTopologicalGeometricVertex (v i), ⟨i, rfl⟩, ?_⟩
    rw [hvj, move23PiLinearMap_basisVertex h, ← hwj]

theorem move23PiLinearMap_image_ABCD {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) :
    move23PiLinearMap a b c d e '' move23PiTetrahedronBody (move23PiABCD a b c d e) =
      move23TetrahedronBody move23BipyramidABCD := by
  apply move23PiLinearMap_image_face h
  intro i; fin_cases i
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩
  · exact ⟨3, rfl, rfl⟩

theorem move23PiLinearMap_image_ABCE {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) :
    move23PiLinearMap a b c d e '' move23PiTetrahedronBody (move23PiABCE a b c d e) =
      move23TetrahedronBody move23BipyramidABCE := by
  apply move23PiLinearMap_image_face h
  intro i; fin_cases i
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩
  · exact ⟨4, rfl, rfl⟩

theorem move23PiLinearMap_image_ABDE {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) :
    move23PiLinearMap a b c d e '' move23PiTetrahedronBody (move23PiABDE a b c d e) =
      move23TetrahedronBody move23BipyramidABDE := by
  apply move23PiLinearMap_image_face h
  intro i; fin_cases i
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨3, rfl, rfl⟩
  · exact ⟨4, rfl, rfl⟩

theorem move23PiLinearMap_image_ACDE {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) :
    move23PiLinearMap a b c d e '' move23PiTetrahedronBody (move23PiACDE a b c d e) =
      move23TetrahedronBody move23BipyramidACDE := by
  apply move23PiLinearMap_image_face h
  intro i; fin_cases i
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩
  · exact ⟨3, rfl, rfl⟩
  · exact ⟨4, rfl, rfl⟩

theorem move23PiLinearMap_image_BCDE {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) :
    move23PiLinearMap a b c d e '' move23PiTetrahedronBody (move23PiBCDE a b c d e) =
      move23TetrahedronBody move23BipyramidBCDE := by
  apply move23PiLinearMap_image_face h
  intro i; fin_cases i
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩
  · exact ⟨3, rfl, rfl⟩
  · exact ⟨4, rfl, rfl⟩

theorem move23PiLinearMap_image_sourceLocalCarrier {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) :
    move23PiLinearMap a b c d e '' move23PiSourceLocalCarrier a b c d e =
      move23BipyramidSourceBody := by
  rw [move23PiSourceLocalCarrier, Set.image_union,
    move23PiLinearMap_image_ABCD h, move23PiLinearMap_image_ABCE h]
  rfl

theorem move23PiLinearMap_image_targetLocalCarrier {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) :
    move23PiLinearMap a b c d e '' move23PiTargetLocalCarrier a b c d e =
      move23BipyramidTargetBody := by
  rw [move23PiTargetLocalCarrier, Set.image_union, Set.image_union,
    move23PiLinearMap_image_ABDE h, move23PiLinearMap_image_ACDE h,
    move23PiLinearMap_image_BCDE h]
  rfl

theorem move23PiLinearMap_source_target_common_image {a b c d e : Nat}
    (h : [a, b, c, d, e].Nodup) :
    move23PiLinearMap a b c d e '' move23PiSourceLocalCarrier a b c d e =
      move23PiLinearMap a b c d e '' move23PiTargetLocalCarrier a b c d e := by
  rw [move23PiLinearMap_image_sourceLocalCarrier h,
    move23PiLinearMap_image_targetLocalCarrier h,
    move23BipyramidSourceBody_eq_targetBody]

theorem ClosedTriangulationCore.move23PiLinearMap_site_common_image
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    move23PiLinearMap s.a s.b s.c s.d s.e ''
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e =
      move23PiLinearMap s.a s.b s.c s.d s.e ''
        move23PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
  apply move23PiLinearMap_source_target_common_image
  exact hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2

end Poincare
