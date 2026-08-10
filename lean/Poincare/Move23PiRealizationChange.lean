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

theorem move23PiTetrahedronBody_isCompact (v : Fin 4 → Nat) :
    IsCompact (move23PiTetrahedronBody v) := by
  exact (Set.toFinite
    (Set.range (fun i =>
      triangulationTopologicalGeometricVertex (v i)))).isCompact_convexHull ℝ

theorem move23PiSourceLocalCarrier_isCompact (a b c d e : Nat) :
    IsCompact (move23PiSourceLocalCarrier a b c d e) := by
  exact (move23PiTetrahedronBody_isCompact _).union
    (move23PiTetrahedronBody_isCompact _)

theorem move23PiTargetLocalCarrier_isCompact (a b c d e : Nat) :
    IsCompact (move23PiTargetLocalCarrier a b c d e) := by
  exact ((move23PiTetrahedronBody_isCompact _).union
    (move23PiTetrahedronBody_isCompact _)).union
      (move23PiTetrahedronBody_isCompact _)

private theorem move23PiTetrahedronBody_coordinate_nonneg
    (v : Fin 4 → Nat) {p : Nat → ℝ} (hp : p ∈ move23PiTetrahedronBody v)
    (z : Nat) : 0 ≤ p z := by
  rw [move23PiTetrahedronBody] at hp
  apply convexHull_min _ (convex_halfSpace_ge
    ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
  rintro _ ⟨i, rfl⟩
  simp [triangulationTopologicalGeometricVertex, Pi.single_apply]
  split <;> positivity

private theorem move23PiTetrahedronBody_sum_labels
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    (v : Fin 4 → Nat)
    (hv : ∀ i, v i = a ∨ v i = b ∨ v i = c ∨ v i = d ∨ v i = e)
    {p : Nat → ℝ} (hp : p ∈ move23PiTetrahedronBody v) :
    p a + p b + p c + p d + p e = 1 := by
  rw [move23PiTetrahedronBody] at hp
  apply convexHull_min _ (convex_hyperplane
    ⟨fun x y ↦ by simp only [Pi.add_apply]; ring,
      fun r x ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring⟩ (1 : ℝ)) hp
  rintro _ ⟨i, rfl⟩
  change triangulationTopologicalGeometricVertex (v i) a +
    triangulationTopologicalGeometricVertex (v i) b +
    triangulationTopologicalGeometricVertex (v i) c +
    triangulationTopologicalGeometricVertex (v i) d +
    triangulationTopologicalGeometricVertex (v i) e = 1
  rcases hv i with hj | hj | hj | hj | hj
  all_goals rw [hj]
  all_goals simp_all [triangulationTopologicalGeometricVertex, List.nodup_cons]

private theorem move23PiTetrahedronBody_coordinate_eq_zero
    (v : Fin 4 → Nat) {p : Nat → ℝ} (hp : p ∈ move23PiTetrahedronBody v)
    (z : Nat) (hz : ∀ i, v i ≠ z) : p z = 0 := by
  rw [move23PiTetrahedronBody] at hp
  apply convexHull_min _ (convex_hyperplane
    ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
  rintro _ ⟨i, rfl⟩
  simp [triangulationTopologicalGeometricVertex, hz i]

theorem move23PiSourceLocalCarrier_nonneg
    {a b c d e : Nat} {p : Nat → ℝ}
    (hp : p ∈ move23PiSourceLocalCarrier a b c d e) (z : Nat) : 0 ≤ p z := by
  rcases hp with hp | hp
  · exact move23PiTetrahedronBody_coordinate_nonneg _ hp z
  · exact move23PiTetrahedronBody_coordinate_nonneg _ hp z

theorem move23PiTargetLocalCarrier_nonneg
    {a b c d e : Nat} {p : Nat → ℝ}
    (hp : p ∈ move23PiTargetLocalCarrier a b c d e) (z : Nat) : 0 ≤ p z := by
  rcases hp with (hp | hp) | hp
  · exact move23PiTetrahedronBody_coordinate_nonneg _ hp z
  · exact move23PiTetrahedronBody_coordinate_nonneg _ hp z
  · exact move23PiTetrahedronBody_coordinate_nonneg _ hp z

theorem move23PiSourceLocalCarrier_sum
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    {p : Nat → ℝ} (hp : p ∈ move23PiSourceLocalCarrier a b c d e) :
    p a + p b + p c + p d + p e = 1 := by
  rcases hp with hp | hp
  · apply move23PiTetrahedronBody_sum_labels h _ _ hp
    intro i; fin_cases i <;> simp [move23PiABCD]
  · apply move23PiTetrahedronBody_sum_labels h _ _ hp
    intro i; fin_cases i <;> simp [move23PiABCE]

theorem move23PiTargetLocalCarrier_sum
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    {p : Nat → ℝ} (hp : p ∈ move23PiTargetLocalCarrier a b c d e) :
    p a + p b + p c + p d + p e = 1 := by
  rcases hp with (hp | hp) | hp
  · apply move23PiTetrahedronBody_sum_labels h _ _ hp
    intro i; fin_cases i <;> simp [move23PiABDE]
  · apply move23PiTetrahedronBody_sum_labels h _ _ hp
    intro i; fin_cases i <;> simp [move23PiACDE]
  · apply move23PiTetrahedronBody_sum_labels h _ _ hp
    intro i; fin_cases i <;> simp [move23PiBCDE]

theorem move23PiSourceLocalCarrier_zero_apex
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    {p : Nat → ℝ} (hp : p ∈ move23PiSourceLocalCarrier a b c d e) :
    p d = 0 ∨ p e = 0 := by
  rcases hp with hp | hp
  · right
    apply move23PiTetrahedronBody_coordinate_eq_zero _ hp
    intro i; fin_cases i <;> simp_all [move23PiABCD, List.nodup_cons] <;> omega
  · left
    apply move23PiTetrahedronBody_coordinate_eq_zero _ hp
    intro i; fin_cases i <;> simp_all [move23PiABCE, List.nodup_cons] <;> omega

theorem move23PiTargetLocalCarrier_zero_base
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    {p : Nat → ℝ} (hp : p ∈ move23PiTargetLocalCarrier a b c d e) :
    p a = 0 ∨ p b = 0 ∨ p c = 0 := by
  rcases hp with (hp | hp) | hp
  · right; right
    apply move23PiTetrahedronBody_coordinate_eq_zero _ hp
    intro i; fin_cases i <;> simp_all [move23PiABDE, List.nodup_cons] <;> omega
  · right; left
    apply move23PiTetrahedronBody_coordinate_eq_zero _ hp
    intro i; fin_cases i <;> simp_all [move23PiACDE, List.nodup_cons] <;> omega
  · left
    apply move23PiTetrahedronBody_coordinate_eq_zero _ hp
    intro i; fin_cases i <;> simp_all [move23PiBCDE, List.nodup_cons] <;> omega

theorem move23PiSourceLocalCarrier_eq_zero_of_not_label
    {a b c d e z : Nat} {p : Nat → ℝ}
    (hp : p ∈ move23PiSourceLocalCarrier a b c d e)
    (ha : z ≠ a) (hb : z ≠ b) (hc : z ≠ c) (hd : z ≠ d) (he : z ≠ e) :
    p z = 0 := by
  rcases hp with hp | hp
  all_goals apply move23PiTetrahedronBody_coordinate_eq_zero _ hp
  all_goals intro i; fin_cases i <;>
    simp_all [move23PiABCD, move23PiABCE] <;> omega

theorem move23PiTargetLocalCarrier_eq_zero_of_not_label
    {a b c d e z : Nat} {p : Nat → ℝ}
    (hp : p ∈ move23PiTargetLocalCarrier a b c d e)
    (ha : z ≠ a) (hb : z ≠ b) (hc : z ≠ c) (hd : z ≠ d) (he : z ≠ e) :
    p z = 0 := by
  rcases hp with (hp | hp) | hp
  all_goals apply move23PiTetrahedronBody_coordinate_eq_zero _ hp
  all_goals intro i; fin_cases i <;>
    simp_all [move23PiABDE, move23PiACDE, move23PiBCDE] <;> omega

theorem move23PiLinearMap_apply_zero (a b c d e : Nat) (p : Nat → ℝ) :
    (move23PiLinearMap a b c d e p) 0 = p a - p c := by
  simp [move23PiLinearMap, move23BipyramidVertex, Fin.sum_univ_succ]
  ring

theorem move23PiLinearMap_apply_one (a b c d e : Nat) (p : Nat → ℝ) :
    (move23PiLinearMap a b c d e p) 1 = p b - p c := by
  simp [move23PiLinearMap, move23BipyramidVertex, Fin.sum_univ_succ]
  ring

theorem move23PiLinearMap_apply_two (a b c d e : Nat) (p : Nat → ℝ) :
    (move23PiLinearMap a b c d e p) 2 = p d - p e := by
  simp [move23PiLinearMap, move23BipyramidVertex, Fin.sum_univ_succ]
  ring

private theorem move23Circuit_differences
    {pa pb pc pd pe qa qb qc qd qe : ℝ}
    (ha : pa - pc = qa - qc) (hb : pb - pc = qb - qc)
    (hde : pd - pe = qd - qe)
    (hp : pa + pb + pc + pd + pe = 1)
    (hq : qa + qb + qc + qd + qe = 1) :
    pa - qa = pb - qb ∧ pa - qa = pc - qc ∧
      pd - qd = pe - qe ∧ 3 * (pa - qa) + 2 * (pd - qd) = 0 := by
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

theorem move23PiLinearMap_injOn_sourceLocalCarrier
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) :
    Set.InjOn (move23PiLinearMap a b c d e)
      (move23PiSourceLocalCarrier a b c d e) := by
  intro p hp q hq hL
  have ha := congrArg (fun x : Move23BipyramidAmbient => x 0) hL
  have hb := congrArg (fun x : Move23BipyramidAmbient => x 1) hL
  have hde := congrArg (fun x : Move23BipyramidAmbient => x 2) hL
  change (move23PiLinearMap a b c d e p) 0 =
    (move23PiLinearMap a b c d e q) 0 at ha
  change (move23PiLinearMap a b c d e p) 1 =
    (move23PiLinearMap a b c d e q) 1 at hb
  change (move23PiLinearMap a b c d e p) 2 =
    (move23PiLinearMap a b c d e q) 2 at hde
  rw [move23PiLinearMap_apply_zero, move23PiLinearMap_apply_zero] at ha
  rw [move23PiLinearMap_apply_one, move23PiLinearMap_apply_one] at hb
  rw [move23PiLinearMap_apply_two, move23PiLinearMap_apply_two] at hde
  have hsumP := move23PiSourceLocalCarrier_sum h hp
  have hsumQ := move23PiSourceLocalCarrier_sum h hq
  obtain ⟨hab, hac, hdep, hcircuit⟩ :=
    move23Circuit_differences ha hb hde hsumP hsumQ
  have hpd := move23PiSourceLocalCarrier_nonneg hp d
  have hpe := move23PiSourceLocalCarrier_nonneg hp e
  have hqd := move23PiSourceLocalCarrier_nonneg hq d
  have hqe := move23PiSourceLocalCarrier_nonneg hq e
  rcases move23PiSourceLocalCarrier_zero_apex h hp with hpd0 | hpe0 <;>
    rcases move23PiSourceLocalCarrier_zero_apex h hq with hqd0 | hqe0
  all_goals
    have haa : p a = q a := by linarith
    have hbb : p b = q b := by linarith
    have hcc : p c = q c := by linarith
    have hdd : p d = q d := by linarith
    have hee : p e = q e := by linarith
    funext z
    by_cases hza : z = a
    · subst z; exact haa
    by_cases hzb : z = b
    · subst z; exact hbb
    by_cases hzc : z = c
    · subst z; exact hcc
    by_cases hzd : z = d
    · subst z; exact hdd
    by_cases hze : z = e
    · subst z; exact hee
    rw [move23PiSourceLocalCarrier_eq_zero_of_not_label hp hza hzb hzc hzd hze,
      move23PiSourceLocalCarrier_eq_zero_of_not_label hq hza hzb hzc hzd hze]

theorem move23PiLinearMap_injOn_targetLocalCarrier
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) :
    Set.InjOn (move23PiLinearMap a b c d e)
      (move23PiTargetLocalCarrier a b c d e) := by
  intro p hp q hq hL
  have ha := congrArg (fun x : Move23BipyramidAmbient => x 0) hL
  have hb := congrArg (fun x : Move23BipyramidAmbient => x 1) hL
  have hde := congrArg (fun x : Move23BipyramidAmbient => x 2) hL
  change (move23PiLinearMap a b c d e p) 0 =
    (move23PiLinearMap a b c d e q) 0 at ha
  change (move23PiLinearMap a b c d e p) 1 =
    (move23PiLinearMap a b c d e q) 1 at hb
  change (move23PiLinearMap a b c d e p) 2 =
    (move23PiLinearMap a b c d e q) 2 at hde
  rw [move23PiLinearMap_apply_zero, move23PiLinearMap_apply_zero] at ha
  rw [move23PiLinearMap_apply_one, move23PiLinearMap_apply_one] at hb
  rw [move23PiLinearMap_apply_two, move23PiLinearMap_apply_two] at hde
  have hsumP := move23PiTargetLocalCarrier_sum h hp
  have hsumQ := move23PiTargetLocalCarrier_sum h hq
  obtain ⟨hab, hac, hdep, hcircuit⟩ :=
    move23Circuit_differences ha hb hde hsumP hsumQ
  have hpa := move23PiTargetLocalCarrier_nonneg hp a
  have hpb := move23PiTargetLocalCarrier_nonneg hp b
  have hpc := move23PiTargetLocalCarrier_nonneg hp c
  have hqa := move23PiTargetLocalCarrier_nonneg hq a
  have hqb := move23PiTargetLocalCarrier_nonneg hq b
  have hqc := move23PiTargetLocalCarrier_nonneg hq c
  rcases move23PiTargetLocalCarrier_zero_base h hp with hpa0 | hpb0 | hpc0 <;>
    rcases move23PiTargetLocalCarrier_zero_base h hq with hqa0 | hqb0 | hqc0
  all_goals
    have haa : p a = q a := by linarith
    have hbb : p b = q b := by linarith
    have hcc : p c = q c := by linarith
    have hdd : p d = q d := by linarith
    have hee : p e = q e := by linarith
    funext z
    by_cases hza : z = a
    · subst z; exact haa
    by_cases hzb : z = b
    · subst z; exact hbb
    by_cases hzc : z = c
    · subst z; exact hcc
    by_cases hzd : z = d
    · subst z; exact hdd
    by_cases hze : z = e
    · subst z; exact hee
    rw [move23PiTargetLocalCarrier_eq_zero_of_not_label hp hza hzb hzc hzd hze,
      move23PiTargetLocalCarrier_eq_zero_of_not_label hq hza hzb hzc hzd hze]

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

noncomputable def move23PiSourceHomeomorphBipyramid
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) :
    ↥(move23PiSourceLocalCarrier a b c d e) ≃ₜ
      ↥move23BipyramidSourceBody := by
  let f : ↥(move23PiSourceLocalCarrier a b c d e) →
      ↥move23BipyramidSourceBody := fun p ↦
    ⟨move23PiLinearMap a b c d e p.1,
      (move23PiLinearMap_image_sourceLocalCarrier h) ▸
        Set.mem_image_of_mem _ p.2⟩
  letI : CompactSpace ↥(move23PiSourceLocalCarrier a b c d e) :=
    isCompact_iff_compactSpace.mp
      (move23PiSourceLocalCarrier_isCompact a b c d e)
  have hfcont : Continuous f :=
    Continuous.subtype_mk
      ((continuous_move23PiLinearMap a b c d e).comp continuous_subtype_val) _
  have hfinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact move23PiLinearMap_injOn_sourceLocalCarrier h
      p.2 q.2 (Subtype.ext_iff.mp hpq)
  have hfsurj : Function.Surjective f := by
    intro q
    have hq : q.1 ∈ move23PiLinearMap a b c d e ''
        move23PiSourceLocalCarrier a b c d e := by
      rw [move23PiLinearMap_image_sourceLocalCarrier h]
      exact q.2
    obtain ⟨p, hp, hpq⟩ := hq
    exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩
  exact IsHomeomorph.homeomorph f
    ((isHomeomorph_iff_continuous_bijective).2 ⟨hfcont, hfinj, hfsurj⟩)

noncomputable def move23PiTargetHomeomorphBipyramid
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) :
    ↥(move23PiTargetLocalCarrier a b c d e) ≃ₜ
      ↥move23BipyramidSourceBody := by
  let f : ↥(move23PiTargetLocalCarrier a b c d e) →
      ↥move23BipyramidSourceBody := fun p ↦
    ⟨move23PiLinearMap a b c d e p.1, by
      rw [move23BipyramidSourceBody_eq_targetBody]
      exact (move23PiLinearMap_image_targetLocalCarrier h) ▸
        Set.mem_image_of_mem _ p.2⟩
  letI : CompactSpace ↥(move23PiTargetLocalCarrier a b c d e) :=
    isCompact_iff_compactSpace.mp
      (move23PiTargetLocalCarrier_isCompact a b c d e)
  have hfcont : Continuous f :=
    Continuous.subtype_mk
      ((continuous_move23PiLinearMap a b c d e).comp continuous_subtype_val) _
  have hfinj : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    exact move23PiLinearMap_injOn_targetLocalCarrier h
      p.2 q.2 (Subtype.ext_iff.mp hpq)
  have hfsurj : Function.Surjective f := by
    intro q
    have hq : q.1 ∈ move23PiLinearMap a b c d e ''
        move23PiTargetLocalCarrier a b c d e := by
      rw [move23PiLinearMap_image_targetLocalCarrier h,
        ← move23BipyramidSourceBody_eq_targetBody]
      exact q.2
    obtain ⟨p, hp, hpq⟩ := hq
    exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩
  exact IsHomeomorph.homeomorph f
    ((isHomeomorph_iff_continuous_bijective).2 ⟨hfcont, hfinj, hfsurj⟩)

noncomputable def move23PiLocalHomeomorph
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) :
    ↥(move23PiSourceLocalCarrier a b c d e) ≃ₜ
      ↥(move23PiTargetLocalCarrier a b c d e) :=
  (move23PiSourceHomeomorphBipyramid h).trans
    (move23PiTargetHomeomorphBipyramid h).symm

theorem move23PiLocalHomeomorph_apply_eq_of_mem_target
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    (p : ↥(move23PiSourceLocalCarrier a b c d e))
    (hpTarget : p.1 ∈ move23PiTargetLocalCarrier a b c d e) :
    (move23PiLocalHomeomorph h p).1 = p.1 := by
  let q : ↥(move23PiTargetLocalCarrier a b c d e) := ⟨p.1, hpTarget⟩
  have heq : move23PiSourceHomeomorphBipyramid h p =
      move23PiTargetHomeomorphBipyramid h q := by
    apply Subtype.ext
    rfl
  have := congrArg (move23PiTargetHomeomorphBipyramid h).symm heq
  simpa [move23PiLocalHomeomorph, q] using Subtype.ext_iff.mp this

theorem move23PiLocalHomeomorph_symm_apply_eq_of_mem_source
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    (q : ↥(move23PiTargetLocalCarrier a b c d e))
    (hqSource : q.1 ∈ move23PiSourceLocalCarrier a b c d e) :
    ((move23PiLocalHomeomorph h).symm q).1 = q.1 := by
  let p : ↥(move23PiSourceLocalCarrier a b c d e) := ⟨q.1, hqSource⟩
  have heq : move23PiSourceHomeomorphBipyramid h p =
      move23PiTargetHomeomorphBipyramid h q := by
    apply Subtype.ext
    rfl
  have := congrArg (move23PiSourceHomeomorphBipyramid h).symm heq
  simpa [move23PiLocalHomeomorph, p] using (Subtype.ext_iff.mp this).symm

noncomputable def ClosedTriangulationCore.move23PiLocalHomeomorph_site
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    ↥(move23PiSourceLocalCarrier s.a s.b s.c s.d s.e) ≃ₜ
      ↥(move23PiTargetLocalCarrier s.a s.b s.c s.d s.e) :=
  move23PiLocalHomeomorph
    (hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2)

theorem ClosedTriangulationCore.move23PiLinearMap_site_common_image
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    move23PiLinearMap s.a s.b s.c s.d s.e ''
        move23PiSourceLocalCarrier s.a s.b s.c s.d s.e =
      move23PiLinearMap s.a s.b s.c s.d s.e ''
        move23PiTargetLocalCarrier s.a s.b s.c s.d s.e := by
  apply move23PiLinearMap_source_target_common_image
  exact hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2

theorem ClosedTriangulationCore.move23PiLinearMap_injOn_site_sourceLocalCarrier
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    Set.InjOn (move23PiLinearMap s.a s.b s.c s.d s.e)
      (move23PiSourceLocalCarrier s.a s.b s.c s.d s.e) := by
  apply move23PiLinearMap_injOn_sourceLocalCarrier
  exact hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2

theorem ClosedTriangulationCore.move23PiLinearMap_injOn_site_targetLocalCarrier
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move23Site) (hlegal : s.LegalIn K) :
    Set.InjOn (move23PiLinearMap s.a s.b s.c s.d s.e)
      (move23PiTargetLocalCarrier s.a s.b s.c s.d s.e) := by
  apply move23PiLinearMap_injOn_targetLocalCarrier
  exact hcore.move23Site_distinct_independent (s := s) hlegal.1 hlegal.2.2

end Poincare
