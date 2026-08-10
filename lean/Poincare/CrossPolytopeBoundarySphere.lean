import Poincare.CrossPolytopeBoundary
import Poincare.FourSimplexSphere
import Poincare.TriangulationTopologicalGeometricCompactness
import Poincare.TriangulationTopologicalGeometricHausdorff
import Poincare.TriangulationTopologicalHonestManifold
import Poincare.TriangulationTopologicalS3
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set
open scoped Manifold
namespace Poincare
noncomputable local instance : DecidableEq (Nat → ℝ) := Classical.decEq _

private theorem convexHull_geometricVertex_coordinate_nonneg
    {F : Finset Nat} {p : Nat → ℝ}
    (hp : p ∈ convexHull ℝ (triangulationTopologicalGeometricVertex '' (↑F : Set Nat)))
    (j : Nat) : 0 ≤ p j := by
  apply convexHull_min _ (convex_halfSpace_ge
    ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
  rintro _ ⟨i, _hi, rfl⟩
  simp [triangulationTopologicalGeometricVertex, Pi.single_apply]
  split <;> norm_num

private theorem convexHull_geometricVertex_sum
    {F : Finset Nat} (hF : F.Nonempty) {p : Nat → ℝ}
    (hp : p ∈ convexHull ℝ (triangulationTopologicalGeometricVertex '' (↑F : Set Nat))) :
    ∑ j ∈ F, p j = 1 := by
  apply convexHull_min _ (convex_hyperplane
    ⟨fun x y ↦ by simp [Finset.sum_add_distrib],
      fun r x ↦ by simp [Finset.mul_sum]⟩ (1 : ℝ)) hp
  rintro _ ⟨i, hi, rfl⟩
  change ∑ j ∈ F, triangulationTopologicalGeometricVertex i j = 1
  rw [Finset.sum_eq_single i]
  · simp [triangulationTopologicalGeometricVertex]
  · intro j hj hji
    simp [triangulationTopologicalGeometricVertex, hji]
  · exact fun h ↦ (h hi).elim

private theorem convexHull_geometricVertex_coordinate_eq_zero
    {F : Finset Nat} {p : Nat → ℝ}
    (hp : p ∈ convexHull ℝ (triangulationTopologicalGeometricVertex '' (↑F : Set Nat)))
    {j : Nat} (hj : j ∉ F) : p j = 0 := by
  apply convexHull_min _ (convex_hyperplane
    ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
  rintro _ ⟨i, hi, rfl⟩
  have hij : i ≠ j := fun h ↦ hj (h ▸ hi)
  simp [triangulationTopologicalGeometricVertex, hij]

theorem crossPolytopeBoundary4_carrier_coordinate_nonneg
    (p : Nat → ℝ)
    (hp : p ∈ (triangulationTopologicalGeometricComplex crossPolytopeBoundary4).space)
    (j : Nat) : 0 ≤ p j := by
  obtain ⟨F, _hF, _hFt, hpF⟩ :=
    (mem_triangulationTopologicalGeometricCarrier_iff _ _).1 hp
  exact convexHull_geometricVertex_coordinate_nonneg hpF j

theorem crossPolytopeBoundary4_carrier_coordinate_eq_zero
    (p : Nat → ℝ)
    (hp : p ∈ (triangulationTopologicalGeometricComplex crossPolytopeBoundary4).space)
    {j : Nat} (hj : 8 ≤ j) : p j = 0 := by
  obtain ⟨F, _hF, ⟨τ, hτ, hFτ⟩, hpF⟩ :=
    (mem_triangulationTopologicalGeometricCarrier_iff _ _).1 hp
  apply convexHull_geometricVertex_coordinate_eq_zero hpF
  intro hjF
  have hjτ := hFτ hjF
  simp only [crossPolytopeBoundary4, List.mem_cons, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Tet.verts] at hjτ <;> omega

theorem crossPolytopeBoundary4_carrier_sum_coordinates
    (p : Nat → ℝ)
    (hp : p ∈ (triangulationTopologicalGeometricComplex crossPolytopeBoundary4).space) :
    ∑ j ∈ Finset.range 8, p j = 1 := by
  obtain ⟨F, hF, ⟨τ, hτ, hFτ⟩, hpF⟩ :=
    (mem_triangulationTopologicalGeometricCarrier_iff _ _).1 hp
  have hsub : F ⊆ Finset.range 8 := by
    intro j hj
    have hjτ := hFτ hj
    simp only [crossPolytopeBoundary4, List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Tet.verts] at hjτ ⊢ <;> omega
  rw [← convexHull_geometricVertex_sum hF hpF]
  symm
  apply Finset.sum_subset hsub
  intro j hjrange hjF
  exact convexHull_geometricVertex_coordinate_eq_zero hpF hjF

theorem crossPolytopeBoundary4_carrier_pairwise_zero
    (p : Nat → ℝ)
    (hp : p ∈ (triangulationTopologicalGeometricComplex crossPolytopeBoundary4).space) :
    (p 0 = 0 ∨ p 1 = 0) ∧ (p 2 = 0 ∨ p 3 = 0) ∧
      (p 4 = 0 ∨ p 5 = 0) ∧ (p 6 = 0 ∨ p 7 = 0) := by
  obtain ⟨F, _hF, ⟨τ, hτ, hFτ⟩, hpF⟩ :=
    (mem_triangulationTopologicalGeometricCarrier_iff _ _).1 hp
  have hz (j : Nat) (hj : j ∉ τ.verts.toFinset) : p j = 0 :=
    convexHull_geometricVertex_coordinate_eq_zero hpF (fun h ↦ hj (hFτ h))
  simp [crossPolytopeBoundary4] at hτ
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Tet.verts] at hz ⊢ <;> aesop

def crossPolytopeL1Sphere : Set (Fin 4 → ℝ) := {u | ∑ i, |u i| = 1}

def crossPolytopeSignedCoordinates (p : Nat → ℝ) : Fin 4 → ℝ :=
  fun i ↦ p (2 * i.val) - p (2 * i.val + 1)

theorem continuous_crossPolytopeSignedCoordinates :
    Continuous crossPolytopeSignedCoordinates := by
  apply continuous_pi
  intro i
  exact (continuous_apply (2 * i.val)).sub (continuous_apply (2 * i.val + 1))

theorem crossPolytopeSignedCoordinates_mem_l1Sphere
    (p : triangulationTopologicalGeometricCarrier crossPolytopeBoundary4) :
    crossPolytopeSignedCoordinates p.1 ∈ crossPolytopeL1Sphere := by
  have hn := crossPolytopeBoundary4_carrier_coordinate_nonneg p.1 p.2
  rcases crossPolytopeBoundary4_carrier_pairwise_zero p.1 p.2 with
    ⟨h01, h23, h45, h67⟩
  have habs (a b : Nat) (h : p.1 a = 0 ∨ p.1 b = 0) :
      |p.1 a - p.1 b| = p.1 a + p.1 b := by
    rcases h with ha | hb
    · rw [ha, zero_sub, abs_neg, abs_of_nonneg (hn b), zero_add]
    · rw [hb, sub_zero, abs_of_nonneg (hn a), add_zero]
  change ∑ i : Fin 4, |p.1 (2 * i.val) - p.1 (2 * i.val + 1)| = 1
  rw [show (∑ i : Fin 4, |p.1 (2 * i.val) - p.1 (2 * i.val + 1)|) =
      ∑ j ∈ Finset.range 8, p.1 j by
    simp [Fin.sum_univ_succ, habs 0 1 h01, habs 2 3 h23,
      habs 4 5 h45, habs 6 7 h67, Finset.sum_range_succ]
    ring]
  exact crossPolytopeBoundary4_carrier_sum_coordinates p.1 p.2

/-- The canonical positive/negative-part inverse, supported on labels zero through seven. -/
def crossPolytopeSignedCoordinatesInverse (u : Fin 4 → ℝ) : Nat → ℝ :=
  fun j ↦
    if j = 0 then max (u 0) 0 else
    if j = 1 then max (-u 0) 0 else
    if j = 2 then max (u 1) 0 else
    if j = 3 then max (-u 1) 0 else
    if j = 4 then max (u 2) 0 else
    if j = 5 then max (-u 2) 0 else
    if j = 6 then max (u 3) 0 else
    if j = 7 then max (-u 3) 0 else 0

private noncomputable def crossPolytopeSignLabel (u : Fin 4 → ℝ) : Fin 4 → Nat
  | 0 => if 0 ≤ u 0 then 0 else 1
  | 1 => if 0 ≤ u 1 then 2 else 3
  | 2 => if 0 ≤ u 2 then 4 else 5
  | 3 => if 0 ≤ u 3 then 6 else 7

private noncomputable def crossPolytopeSignTet (u : Fin 4 → ℝ) : Tet :=
  ⟨crossPolytopeSignLabel u 0, crossPolytopeSignLabel u 1,
    crossPolytopeSignLabel u 2, crossPolytopeSignLabel u 3⟩

set_option maxHeartbeats 1000000 in
theorem crossPolytopeSignedCoordinatesInverse_mem_carrier
    (u : ↥crossPolytopeL1Sphere) :
    crossPolytopeSignedCoordinatesInverse u.1 ∈
      (triangulationTopologicalGeometricComplex crossPolytopeBoundary4).space := by
  classical
  let τ := crossPolytopeSignTet u.1
  have hτ : τ ∈ crossPolytopeBoundary4.tets := by
    unfold τ crossPolytopeSignTet crossPolytopeSignLabel
    simp only [crossPolytopeBoundary4, List.mem_cons, List.not_mem_nil, or_false]
    by_cases h0 : 0 ≤ u.1 0 <;> by_cases h1 : 0 ≤ u.1 1 <;>
      by_cases h2 : 0 ≤ u.1 2 <;> by_cases h3 : 0 ≤ u.1 3 <;>
      simp [h0, h1, h2, h3]
  apply (mem_triangulationTopologicalGeometricCarrier_iff _ _).2
  refine ⟨τ.verts.toFinset, ⟨τ.v0, by simp [Tet.verts]⟩,
    ⟨τ, hτ, Finset.Subset.rfl⟩, ?_⟩
  apply mem_convexHull_of_exists_fintype
    (fun i : Fin 4 ↦ |u.1 i|)
    (fun i : Fin 4 ↦ triangulationTopologicalGeometricVertex
      (crossPolytopeSignLabel u.1 i))
  · exact fun i ↦ abs_nonneg _
  · exact u.2
  · intro i
    refine ⟨crossPolytopeSignLabel u.1 i, ?_, rfl⟩
    change crossPolytopeSignLabel u.1 i ∈ τ.verts.toFinset
    fin_cases i <;> simp [τ, crossPolytopeSignTet, Tet.verts]
  · have hpos (x : ℝ) (h : 0 ≤ x) : |x| = max x 0 := by
      rw [abs_of_nonneg h, max_eq_left h]
    have hneg (x : ℝ) (h : ¬ 0 ≤ x) : |x| = max (-x) 0 := by
      rw [abs_of_neg (lt_of_not_ge h), max_eq_left]
      exact neg_nonneg.mpr (le_of_not_ge h)
    funext j
    by_cases hj : j < 8
    · interval_cases j <;>
        simp [Fin.sum_univ_succ, crossPolytopeSignedCoordinatesInverse,
          triangulationTopologicalGeometricVertex, crossPolytopeSignLabel] <;>
        (by_cases h0 : 0 ≤ u.1 0 <;> by_cases h1 : 0 ≤ u.1 1 <;>
          by_cases h2 : 0 ≤ u.1 2 <;> by_cases h3 : 0 ≤ u.1 3 <;>
          simp [h0, h1, h2, h3, Pi.single_apply,
            hpos, hneg] <;>
          first | exact le_of_not_ge h0 | exact le_of_not_ge h1 |
            exact le_of_not_ge h2 | exact le_of_not_ge h3)
    · have hj0 : j ≠ 0 := by omega
      have hj1 : j ≠ 1 := by omega
      have hj2 : j ≠ 2 := by omega
      have hj3 : j ≠ 3 := by omega
      have hj4 : j ≠ 4 := by omega
      have hj5 : j ≠ 5 := by omega
      have hj6 : j ≠ 6 := by omega
      have hj7 : j ≠ 7 := by omega
      by_cases h0 : 0 ≤ u.1 0 <;> by_cases h1 : 0 ≤ u.1 1 <;>
        by_cases h2 : 0 ≤ u.1 2 <;> by_cases h3 : 0 ≤ u.1 3 <;>
        simp [Fin.sum_univ_succ, crossPolytopeSignedCoordinatesInverse,
          triangulationTopologicalGeometricVertex, crossPolytopeSignLabel,
          Pi.single_apply, h0, h1, h2, h3, hj0, hj1, hj2, hj3,
          hj4, hj5, hj6, hj7]

theorem crossPolytopeSignedCoordinates_inverse (u : Fin 4 → ℝ) :
    crossPolytopeSignedCoordinates
      (crossPolytopeSignedCoordinatesInverse u) = u := by
  funext i
  fin_cases i <;>
    simp [crossPolytopeSignedCoordinates, crossPolytopeSignedCoordinatesInverse,
      max_zero_sub_max_neg_zero_eq_self]

private theorem max_sub_zero_pair
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : a = 0 ∨ b = 0) :
    max (a - b) 0 = a ∧ max (-(a - b)) 0 = b := by
  rcases hz with rfl | rfl <;> simp [ha, hb]

theorem crossPolytopeSignedCoordinatesInverse_signed
    (p : triangulationTopologicalGeometricCarrier crossPolytopeBoundary4) :
    crossPolytopeSignedCoordinatesInverse
        (crossPolytopeSignedCoordinates p.1) = p.1 := by
  have hn := crossPolytopeBoundary4_carrier_coordinate_nonneg p.1 p.2
  rcases crossPolytopeBoundary4_carrier_pairwise_zero p.1 p.2 with
    ⟨h01, h23, h45, h67⟩
  have r01 := max_sub_zero_pair (hn 0) (hn 1) h01
  have r23 := max_sub_zero_pair (hn 2) (hn 3) h23
  have r45 := max_sub_zero_pair (hn 4) (hn 5) h45
  have r67 := max_sub_zero_pair (hn 6) (hn 7) h67
  funext j
  by_cases hj : j < 8
  · interval_cases j
    · change max (p.1 0 - p.1 1) 0 = p.1 0
      exact r01.1
    · change max (-(p.1 0 - p.1 1)) 0 = p.1 1
      exact r01.2
    · change max (p.1 2 - p.1 3) 0 = p.1 2
      exact r23.1
    · change max (-(p.1 2 - p.1 3)) 0 = p.1 3
      exact r23.2
    · change max (p.1 4 - p.1 5) 0 = p.1 4
      exact r45.1
    · change max (-(p.1 4 - p.1 5)) 0 = p.1 5
      exact r45.2
    · change max (p.1 6 - p.1 7) 0 = p.1 6
      exact r67.1
    · change max (-(p.1 6 - p.1 7)) 0 = p.1 7
      exact r67.2
  · have hz :=
      crossPolytopeBoundary4_carrier_coordinate_eq_zero p.1 p.2
        (show 8 ≤ j by omega)
    simp [crossPolytopeSignedCoordinatesInverse, hz,
      show j ≠ 0 by omega, show j ≠ 1 by omega,
      show j ≠ 2 by omega, show j ≠ 3 by omega,
      show j ≠ 4 by omega, show j ≠ 5 by omega,
      show j ≠ 6 by omega, show j ≠ 7 by omega]

theorem continuous_crossPolytopeSignedCoordinatesInverse :
    Continuous crossPolytopeSignedCoordinatesInverse := by
  apply continuous_pi
  intro j
  by_cases hj : j < 8
  · interval_cases j <;>
      norm_num [crossPolytopeSignedCoordinatesInverse] <;> fun_prop
  · have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    have hj2 : j ≠ 2 := by omega
    have hj3 : j ≠ 3 := by omega
    have hj4 : j ≠ 4 := by omega
    have hj5 : j ≠ 5 := by omega
    have hj6 : j ≠ 6 := by omega
    have hj7 : j ≠ 7 := by omega
    simpa [crossPolytopeSignedCoordinatesInverse, hj0, hj1, hj2, hj3,
      hj4, hj5, hj6, hj7] using
      (continuous_const : Continuous (fun _ : Fin 4 → ℝ ↦ (0 : ℝ)))

def crossPolytopeCarrierToL1 :
    triangulationTopologicalGeometricCarrier crossPolytopeBoundary4 →
      ↥crossPolytopeL1Sphere :=
  fun p ↦ ⟨crossPolytopeSignedCoordinates p.1,
    crossPolytopeSignedCoordinates_mem_l1Sphere p⟩

def crossPolytopeL1ToCarrier :
    ↥crossPolytopeL1Sphere →
      triangulationTopologicalGeometricCarrier crossPolytopeBoundary4 :=
  fun u ↦ ⟨crossPolytopeSignedCoordinatesInverse u.1,
    crossPolytopeSignedCoordinatesInverse_mem_carrier u⟩

theorem continuous_crossPolytopeCarrierToL1 :
    Continuous crossPolytopeCarrierToL1 := by
  exact Continuous.subtype_mk
    (continuous_crossPolytopeSignedCoordinates.comp continuous_subtype_val) _

theorem continuous_crossPolytopeL1ToCarrier :
    Continuous crossPolytopeL1ToCarrier := by
  exact Continuous.subtype_mk
    (continuous_crossPolytopeSignedCoordinatesInverse.comp continuous_subtype_val) _

noncomputable def crossPolytopeCarrierHomeomorphL1Sphere :
    triangulationTopologicalGeometricCarrier crossPolytopeBoundary4 ≃ₜ
      ↥crossPolytopeL1Sphere where
  toEquiv :=
    { toFun := crossPolytopeCarrierToL1
      invFun := crossPolytopeL1ToCarrier
      left_inv := fun p ↦ Subtype.ext (crossPolytopeSignedCoordinatesInverse_signed p)
      right_inv := fun u ↦ Subtype.ext (crossPolytopeSignedCoordinates_inverse u.1) }
  continuous_toFun := continuous_crossPolytopeCarrierToL1
  continuous_invFun := continuous_crossPolytopeL1ToCarrier

private noncomputable def crossPolytopeAmbientEquiv :
    (Fin 4 → ℝ) ≃L[ℝ] ThreeSphereAmbient :=
  (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm.toContinuousLinearEquiv

private def crossPolytopeL1Norm (u : Fin 4 → ℝ) : ℝ :=
  ∑ i, |u i|

private theorem crossPolytopeL1Norm_smul (a : ℝ) (u : Fin 4 → ℝ) :
    crossPolytopeL1Norm (a • u) = |a| * crossPolytopeL1Norm u := by
  simp [crossPolytopeL1Norm, abs_mul, Finset.mul_sum]

private theorem continuous_crossPolytopeL1Norm :
    Continuous crossPolytopeL1Norm := by
  unfold crossPolytopeL1Norm
  fun_prop

/-- Radial normalization identifies the four-dimensional L1 sphere with the
genuine Euclidean unit three-sphere. -/
noncomputable def crossPolytopeL1SphereHomeomorphThreeSphere :
    ↥crossPolytopeL1Sphere ≃ₜ
      ↥(Metric.sphere (0 : ThreeSphereAmbient) 1) := by
  let E : (Fin 4 → ℝ) ≃L[ℝ] ThreeSphereAmbient := crossPolytopeAmbientEquiv
  let toFun : ↥crossPolytopeL1Sphere →
      ↥(Metric.sphere (0 : ThreeSphereAmbient) 1) := fun u =>
    ⟨‖E u.1‖⁻¹ • E u.1, by
      have hu0 : u.1 ≠ 0 := by
        intro h
        have := u.2
        simp [crossPolytopeL1Sphere, h] at this
      have hE0 : E u.1 ≠ 0 := E.injective.ne hu0
      simp [Metric.mem_sphere, norm_smul, hE0]⟩
  let invFun : ↥(Metric.sphere (0 : ThreeSphereAmbient) 1) →
      ↥crossPolytopeL1Sphere := fun x =>
    ⟨(crossPolytopeL1Norm (E.symm x.1))⁻¹ • E.symm x.1, by
      have hx0 : x.1 ≠ 0 := by
        intro h
        have := x.2
        simp [Metric.mem_sphere, h] at this
      have hv0 : E.symm x.1 ≠ 0 := E.symm.injective.ne hx0
      have hl1pos : 0 < crossPolytopeL1Norm (E.symm x.1) := by
        rw [crossPolytopeL1Norm]
        apply Finset.sum_pos'
        · exact fun i _ => abs_nonneg _
        · by_contra h
          push_neg at h
          apply hv0
          funext i
          exact abs_eq_zero.mp
            (le_antisymm (h i (Finset.mem_univ i)) (abs_nonneg _))
      change crossPolytopeL1Norm
          ((crossPolytopeL1Norm (E.symm x.1))⁻¹ • E.symm x.1) = 1
      rw [crossPolytopeL1Norm_smul, abs_of_pos (inv_pos.mpr hl1pos)]
      exact inv_mul_cancel₀ hl1pos.ne'⟩
  refine
    { toEquiv :=
        { toFun := toFun
          invFun := invFun
          left_inv := ?_
          right_inv := ?_ }
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro u
    apply Subtype.ext
    have hu0 : u.1 ≠ 0 := by
      intro h
      have := u.2
      simp [crossPolytopeL1Sphere, h] at this
    have hE0 : E u.1 ≠ 0 := E.injective.ne hu0
    have hnpos : 0 < ‖E u.1‖ := norm_pos_iff.mpr hE0
    have hu1 : crossPolytopeL1Norm u.1 = 1 := u.2
    simp [toFun, invFun, E, crossPolytopeL1Norm_smul, hu1,
      abs_of_pos hnpos, hnpos.ne', smul_smul]
  · intro x
    apply Subtype.ext
    have hxnorm : ‖x.1‖ = 1 := by simpa [Metric.mem_sphere] using x.2
    have hx0 : x.1 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hxnorm
      norm_num at hxnorm
    have hv0 : E.symm x.1 ≠ 0 := E.symm.injective.ne hx0
    have hl1pos : 0 < crossPolytopeL1Norm (E.symm x.1) := by
      rw [crossPolytopeL1Norm]
      apply Finset.sum_pos'
      · exact fun i _ => abs_nonneg _
      · by_contra h
        push_neg at h
        apply hv0
        funext i
        exact abs_eq_zero.mp
          (le_antisymm (h i (Finset.mem_univ i)) (abs_nonneg _))
    simp [toFun, invFun, E, crossPolytopeL1Norm_smul, abs_of_pos hl1pos,
      hl1pos.ne', hxnorm, norm_smul, smul_smul]
  · apply Continuous.subtype_mk
    dsimp [toFun]
    apply Continuous.smul
    · apply Continuous.inv₀
      · exact E.continuous.norm.comp continuous_subtype_val
      · intro u hu
        have hE0 : E u.1 ≠ 0 := E.injective.ne (by
          intro h
          have := u.2
          simp [crossPolytopeL1Sphere, h] at this)
        exact hE0 (norm_eq_zero.mp hu)
    · exact E.continuous.comp continuous_subtype_val
  · apply Continuous.subtype_mk
    dsimp [invFun]
    apply Continuous.smul
    · apply Continuous.inv₀
      · exact continuous_crossPolytopeL1Norm.comp
          (E.symm.continuous.comp continuous_subtype_val)
      · intro x hx
        have hx0 : x.1 ≠ 0 := by
          intro h
          have := x.2
          simp [h] at this
        have hv0 : E.symm x.1 ≠ 0 := E.symm.injective.ne hx0
        apply hv0
        funext i
        have hi : |E.symm x.1 i| = 0 := by
          exact Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)
            |>.mp hx i (Finset.mem_univ i)
        simpa using hi
    · exact E.symm.continuous.comp continuous_subtype_val

theorem crossPolytopeBoundary4_realizationHomeomorphicToThreeSphere :
    TriangulationRealizationHomeomorphicToThreeSphere
      crossPolytopeBoundary4 := by
  exact ⟨crossPolytopeCarrierHomeomorphL1Sphere.trans
    crossPolytopeL1SphereHomeomorphThreeSphere⟩

theorem crossPolytopeBoundary4_honestThreeManifold :
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold
      crossPolytopeBoundary4 := by
  let C := triangulationTopologicalGeometricCarrier crossPolytopeBoundary4
  let S := ↥(Metric.sphere (0 : ThreeSphereAmbient) 1)
  let h : C ≃ₜ S := crossPolytopeCarrierHomeomorphL1Sphere.trans
    crossPolytopeL1SphereHomeomorphThreeSphere
  letI : Nonempty S := ⟨⟨PiLp.single 2 (0 : Fin 4) (1 : ℝ), by
    simp [Metric.mem_sphere, PiLp.norm_single]⟩⟩
  letI : Nonempty C := ⟨h.symm (Classical.choice (inferInstance : Nonempty S))⟩
  let sphereCharted : ChartedSpace ThreeManifoldModel S := inferInstance
  let carrierSphereCharted : ChartedSpace S C :=
    h.isOpenEmbedding.singletonChartedSpace
  let carrierCharted : ChartedSpace ThreeManifoldModel C :=
    @ChartedSpace.comp ThreeManifoldModel _ S _ C _
      sphereCharted carrierSphereCharted
  letI : ChartedSpace ThreeManifoldModel C := carrierCharted
  have hmanifold : IsManifold (𝓡 3) 0 C := IsManifold.mk' _ _ _
  have hsphere : IsConnected
      (Metric.sphere (0 : ThreeSphereAmbient) 1) := by
    apply isConnected_sphere
    · rw [(WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).rank_eq,
        rank_fin_fun]
      norm_num
    · norm_num
  letI : ConnectedSpace S := isConnected_iff_connectedSpace.mp hsphere
  have hconnected : IsConnected (Set.univ : Set C) := by
    simpa using (h.isConnected_preimage (s := Set.univ)).mpr isConnected_univ
  exact ⟨inferInstance, carrierCharted, hmanifold,
    triangulationTopologicalGeometricCarrier_univ_isCompact
      crossPolytopeBoundary4, hconnected⟩

theorem exists_honestThreeManifold_positive_PhiSupport_without_strict_move32 :
    ∃ K : Triangulation,
      ClosedTriangulationCore K ∧
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K ∧
      0 < PhiSupport K ∧
      ¬ ∃ s : Move32Site, s.LegalIn K ∧
        PhiSupport (s.replace K) < PhiSupport K := by
  exact ⟨crossPolytopeBoundary4,
    crossPolytopeBoundary4_closedCore,
    crossPolytopeBoundary4_honestThreeManifold,
    crossPolytopeBoundary4_PhiSupport_pos,
    crossPolytopeBoundary4_no_strict_move32⟩

end Poincare
