import Poincare.Move41CombinatorialFoundation
import Poincare.Move23PiRealizationChange

open Set

namespace Poincare

/-- The genuine `4 → 1` source region: the cone from `e` over the four
triangular faces of the tetrahedron on `a,b,c,d`. -/
noncomputable def move41PiSourceLocalCarrier (a b c d e : Nat) : Set (Nat → ℝ) :=
  move23PiTetrahedronBody (move23PiABCE a b c d e) ∪
    move23PiTetrahedronBody (move23PiABDE a b c d e) ∪
      move23PiTetrahedronBody (move23PiACDE a b c d e) ∪
        move23PiTetrahedronBody (move23PiBCDE a b c d e)

/-- The genuine `4 → 1` target region: the solid tetrahedron on the four
outer vertices. -/
noncomputable def move41PiTargetLocalCarrier (a b c d e : Nat) : Set (Nat → ℝ) :=
  move23PiTetrahedronBody (move23PiABCD a b c d e)

/-- The four-tetrahedron source region of a genuine `4 → 1` move is
compact.  This is the closed-piece input used when the explicit barycentric
local homeomorphism is glued to the identity off the move region. -/
theorem move41PiSourceLocalCarrier_isCompact (a b c d e : Nat) :
    IsCompact (move41PiSourceLocalCarrier a b c d e) := by
  exact (((move23PiTetrahedronBody_isCompact _).union
    (move23PiTetrahedronBody_isCompact _)).union
      (move23PiTetrahedronBody_isCompact _)).union
        (move23PiTetrahedronBody_isCompact _)

/-- The solid tetrahedron forming the target region of a genuine `4 → 1`
move is compact. -/
theorem move41PiTargetLocalCarrier_isCompact (a b c d e : Nat) :
    IsCompact (move41PiTargetLocalCarrier a b c d e) := by
  exact move23PiTetrahedronBody_isCompact _

/-- Every barycentric coordinate is nonnegative on the genuine `4 → 1`
source region. -/
theorem move41PiSourceLocalCarrier_nonneg
    {a b c d e : Nat} {p : Nat → ℝ}
    (hp : p ∈ move41PiSourceLocalCarrier a b c d e) (z : Nat) :
    0 ≤ p z := by
  rcases hp with ((hp | hp) | hp) | hp
  · exact move23PiSourceLocalCarrier_nonneg (Or.inr hp) z
  · exact move23PiTargetLocalCarrier_nonneg (Or.inl (Or.inl hp)) z
  · exact move23PiTargetLocalCarrier_nonneg (Or.inl (Or.inr hp)) z
  · exact move23PiTargetLocalCarrier_nonneg (Or.inr hp) z

/-- The barycentric coordinates of every point in the genuine `4 → 1`
source region sum to one over its five labels. -/
theorem move41PiSourceLocalCarrier_sum
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    {p : Nat → ℝ} (hp : p ∈ move41PiSourceLocalCarrier a b c d e) :
    p a + p b + p c + p d + p e = 1 := by
  rcases hp with ((hp | hp) | hp) | hp
  · exact move23PiSourceLocalCarrier_sum h (Or.inr hp)
  · exact move23PiTargetLocalCarrier_sum h (Or.inl (Or.inl hp))
  · exact move23PiTargetLocalCarrier_sum h (Or.inl (Or.inr hp))
  · exact move23PiTargetLocalCarrier_sum h (Or.inr hp)

/-- A point of the genuine `4 → 1` source cone lies over the boundary of
the outer tetrahedron: at least one outer barycentric coordinate vanishes. -/
theorem move41PiSourceLocalCarrier_zero_outer
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    {p : Nat → ℝ} (hp : p ∈ move41PiSourceLocalCarrier a b c d e) :
    p a = 0 ∨ p b = 0 ∨ p c = 0 ∨ p d = 0 := by
  rcases hp with ((hp | hp) | hp) | hp
  · right; right; right
    rw [move23PiTetrahedronBody] at hp
    apply convexHull_min _ (convex_hyperplane
      ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
    rintro _ ⟨i, rfl⟩
    fin_cases i <;>
      simp_all [move23PiABCE, triangulationTopologicalGeometricVertex,
        List.nodup_cons]
  · right; right; left
    rw [move23PiTetrahedronBody] at hp
    apply convexHull_min _ (convex_hyperplane
      ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
    rintro _ ⟨i, rfl⟩
    fin_cases i <;>
      simp_all [move23PiABDE, triangulationTopologicalGeometricVertex,
        List.nodup_cons]
  · right; left
    rw [move23PiTetrahedronBody] at hp
    apply convexHull_min _ (convex_hyperplane
      ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
    rintro _ ⟨i, rfl⟩
    fin_cases i <;>
      simp_all [move23PiACDE, triangulationTopologicalGeometricVertex,
        List.nodup_cons]
  · left
    rw [move23PiTetrahedronBody] at hp
    apply convexHull_min _ (convex_hyperplane
      ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
    rintro _ ⟨i, rfl⟩
    fin_cases i <;>
      simp_all [move23PiBCDE, triangulationTopologicalGeometricVertex,
        List.nodup_cons]

/-- The center barycentric coordinate vanishes throughout the target solid
tetrahedron of a genuine `4 → 1` move. -/
theorem move41PiTargetLocalCarrier_center_eq_zero
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    {p : Nat → ℝ} (hp : p ∈ move41PiTargetLocalCarrier a b c d e) :
    p e = 0 := by
  rw [move41PiTargetLocalCarrier, move23PiTetrahedronBody] at hp
  apply convexHull_min _ (convex_hyperplane
    ⟨fun x y ↦ rfl, fun r x ↦ rfl⟩ (0 : ℝ)) hp
  rintro _ ⟨i, rfl⟩
  fin_cases i <;>
    simp_all [move23PiABCD, triangulationTopologicalGeometricVertex,
      List.nodup_cons]

/-- Every barycentric coordinate is nonnegative on the solid target
tetrahedron of a genuine `4 → 1` move. -/
theorem move41PiTargetLocalCarrier_nonneg
    {a b c d e : Nat} {p : Nat → ℝ}
    (hp : p ∈ move41PiTargetLocalCarrier a b c d e) (z : Nat) :
    0 ≤ p z := by
  exact move23PiSourceLocalCarrier_nonneg (Or.inl hp) z

/-- The barycentric coordinates of every point in the solid target
tetrahedron of a genuine `4 → 1` move sum to one over the five labels. -/
theorem move41PiTargetLocalCarrier_sum
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup)
    {p : Nat → ℝ} (hp : p ∈ move41PiTargetLocalCarrier a b c d e) :
    p a + p b + p c + p d + p e = 1 := by
  exact move23PiSourceLocalCarrier_sum h (Or.inl hp)

/-- Every coordinate outside the five move labels vanishes on the genuine
`4 → 1` source region. -/
theorem move41PiSourceLocalCarrier_eq_zero_of_not_label
    {a b c d e : Nat} {p : Nat → ℝ}
    (hp : p ∈ move41PiSourceLocalCarrier a b c d e)
    {z : Nat} (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (hzd : z ≠ d) (hze : z ≠ e) :
    p z = 0 := by
  rcases hp with ((hp | hp) | hp) | hp
  · exact move23PiSourceLocalCarrier_eq_zero_of_not_label
      (Or.inr hp) hza hzb hzc hzd hze
  · exact move23PiTargetLocalCarrier_eq_zero_of_not_label
      (Or.inl (Or.inl hp)) hza hzb hzc hzd hze
  · exact move23PiTargetLocalCarrier_eq_zero_of_not_label
      (Or.inl (Or.inr hp)) hza hzb hzc hzd hze
  · exact move23PiTargetLocalCarrier_eq_zero_of_not_label
      (Or.inr hp) hza hzb hzc hzd hze

/-- Every coordinate outside the four outer labels vanishes on the solid
target tetrahedron of a genuine `4 → 1` move. -/
theorem move41PiTargetLocalCarrier_eq_zero_of_not_outer_label
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) {p : Nat → ℝ}
    (hp : p ∈ move41PiTargetLocalCarrier a b c d e)
    {z : Nat} (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (hzd : z ≠ d) :
    p z = 0 := by
  by_cases hze : z = e
  · subst z
    exact move41PiTargetLocalCarrier_center_eq_zero h hp
  · exact move23PiSourceLocalCarrier_eq_zero_of_not_label
      (Or.inl hp) hza hzb hzc hzd hze

/-- The barycentric coordinate conditions for the boundary cone are also
sufficient for membership in the genuine `4 → 1` source region. -/
theorem mem_move41PiSourceLocalCarrier_of_coordinates
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) {p : Nat → ℝ}
    (hnonneg : ∀ z, 0 ≤ p z)
    (hsum : p a + p b + p c + p d + p e = 1)
    (hzero : p a = 0 ∨ p b = 0 ∨ p c = 0 ∨ p d = 0)
    (hoff : ∀ {z}, z ≠ a → z ≠ b → z ≠ c → z ≠ d → z ≠ e → p z = 0) :
    p ∈ move41PiSourceLocalCarrier a b c d e := by
  rcases hzero with ha | hb | hc | hd
  · rw [move41PiSourceLocalCarrier]
    refine Or.inr ?_
    apply mem_convexHull_of_exists_fintype (R := ℝ)
        (fun i : Fin 4 ↦ p (move23PiBCDE a b c d e i))
        (fun i ↦ triangulationTopologicalGeometricVertex
          (move23PiBCDE a b c d e i))
    · exact fun i ↦ hnonneg _
    · simp [Fin.sum_univ_four, move23PiBCDE]
      linarith
    · exact fun i ↦ ⟨i, rfl⟩
    · funext z
      simp only [Fin.sum_univ_four, move23PiBCDE, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      simp [triangulationTopologicalGeometricVertex]
      by_cases hzb : z = b
      · subst z; simp_all [List.nodup_cons]
      by_cases hzc : z = c
      · subst z; simp_all [List.nodup_cons]
      by_cases hzd : z = d
      · subst z; simp_all [List.nodup_cons]
      by_cases hze : z = e
      · subst z; simp_all [List.nodup_cons]
      by_cases hza : z = a
      · subst z; simp_all
      simp [hzb, hzc, hzd, hze, hoff hza hzb hzc hzd hze]
  · rw [move41PiSourceLocalCarrier]
    refine Or.inl (Or.inr ?_)
    apply mem_convexHull_of_exists_fintype (R := ℝ)
        (fun i : Fin 4 ↦ p (move23PiACDE a b c d e i))
        (fun i ↦ triangulationTopologicalGeometricVertex
          (move23PiACDE a b c d e i))
    · exact fun i ↦ hnonneg _
    · simp [Fin.sum_univ_four, move23PiACDE]; linarith
    · exact fun i ↦ ⟨i, rfl⟩
    · funext z
      simp only [Fin.sum_univ_four, move23PiACDE, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      simp [triangulationTopologicalGeometricVertex]
      by_cases hza : z = a
      · subst z; simp_all [List.nodup_cons]
      by_cases hzc : z = c
      · subst z; simp_all [List.nodup_cons]
      by_cases hzd : z = d
      · subst z; simp_all [List.nodup_cons]
      by_cases hze : z = e
      · subst z; simp_all [List.nodup_cons]
      by_cases hzb : z = b
      · subst z; simp_all
      simp [hza, hzc, hzd, hze, hoff hza hzb hzc hzd hze]
  · rw [move41PiSourceLocalCarrier]
    refine Or.inl (Or.inl (Or.inr ?_))
    apply mem_convexHull_of_exists_fintype (R := ℝ)
        (fun i : Fin 4 ↦ p (move23PiABDE a b c d e i))
        (fun i ↦ triangulationTopologicalGeometricVertex
          (move23PiABDE a b c d e i))
    · exact fun i ↦ hnonneg _
    · simp [Fin.sum_univ_four, move23PiABDE]; linarith
    · exact fun i ↦ ⟨i, rfl⟩
    · funext z
      simp only [Fin.sum_univ_four, move23PiABDE, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      simp [triangulationTopologicalGeometricVertex]
      by_cases hza : z = a
      · subst z; simp_all [List.nodup_cons]
      by_cases hzb : z = b
      · subst z; simp_all [List.nodup_cons]
      by_cases hzd : z = d
      · subst z; simp_all [List.nodup_cons]
      by_cases hze : z = e
      · subst z; simp_all [List.nodup_cons]
      by_cases hzc : z = c
      · subst z; simp_all
      simp [hza, hzb, hzd, hze, hoff hza hzb hzc hzd hze]
  · rw [move41PiSourceLocalCarrier]
    refine Or.inl (Or.inl (Or.inl ?_))
    apply mem_convexHull_of_exists_fintype (R := ℝ)
        (fun i : Fin 4 ↦ p (move23PiABCE a b c d e i))
        (fun i ↦ triangulationTopologicalGeometricVertex
          (move23PiABCE a b c d e i))
    · exact fun i ↦ hnonneg _
    · simp [Fin.sum_univ_four, move23PiABCE]; linarith
    · exact fun i ↦ ⟨i, rfl⟩
    · funext z
      simp only [Fin.sum_univ_four, move23PiABCE, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      simp [triangulationTopologicalGeometricVertex]
      by_cases hza : z = a
      · subst z; simp_all [List.nodup_cons]
      by_cases hzb : z = b
      · subst z; simp_all [List.nodup_cons]
      by_cases hzc : z = c
      · subst z; simp_all [List.nodup_cons]
      by_cases hze : z = e
      · subst z; simp_all [List.nodup_cons]
      by_cases hzd : z = d
      · subst z; simp_all
      simp [hza, hzb, hzc, hze, hoff hza hzb hzc hzd hze]

/-- The barycentric coordinate conditions for the solid outer tetrahedron
are sufficient for membership in the genuine `4 → 1` target region. -/
theorem mem_move41PiTargetLocalCarrier_of_coordinates
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) {p : Nat → ℝ}
    (hnonneg : ∀ z, 0 ≤ p z)
    (hsum : p a + p b + p c + p d + p e = 1)
    (he : p e = 0)
    (hoff : ∀ {z}, z ≠ a → z ≠ b → z ≠ c → z ≠ d → p z = 0) :
    p ∈ move41PiTargetLocalCarrier a b c d e := by
  rw [move41PiTargetLocalCarrier]
  apply mem_convexHull_of_exists_fintype (R := ℝ)
      (fun i : Fin 4 ↦ p (move23PiABCD a b c d e i))
      (fun i ↦ triangulationTopologicalGeometricVertex
        (move23PiABCD a b c d e i))
  · exact fun i ↦ hnonneg _
  · simp [Fin.sum_univ_four, move23PiABCD]
    linarith
  · exact fun i ↦ ⟨i, rfl⟩
  · funext z
    simp only [Fin.sum_univ_four, move23PiABCD, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    simp [triangulationTopologicalGeometricVertex]
    by_cases hza : z = a
    · subst z; simp_all [List.nodup_cons]
    by_cases hzb : z = b
    · subst z; simp_all [List.nodup_cons]
    by_cases hzc : z = c
    · subst z; simp_all [List.nodup_cons]
    by_cases hzd : z = d
    · subst z; simp_all [List.nodup_cons]
    simp [hza, hzb, hzc, hzd, hoff hza hzb hzc hzd]

/-- The radial barycentric map from the cone on the outer tetrahedral
boundary to the solid outer tetrahedron.  It sends the cone point `e` to
the barycenter and fixes the boundary pointwise. -/
noncomputable def move41PiRadialMap (a b c d e : Nat) (p : Nat → ℝ) :
    Nat → ℝ := fun z ↦
  if z = a then p a + p e / 4
  else if z = b then p b + p e / 4
  else if z = c then p c + p e / 4
  else if z = d then p d + p e / 4
  else 0

/-- The explicit radial barycentric map carries every point of the genuine
`4 → 1` source cone into the solid target tetrahedron. -/
theorem move41PiRadialMap_mem_target
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) {p : Nat → ℝ}
    (hp : p ∈ move41PiSourceLocalCarrier a b c d e) :
    move41PiRadialMap a b c d e p ∈
      move41PiTargetLocalCarrier a b c d e := by
  have hnonneg := move41PiSourceLocalCarrier_nonneg hp
  have hsum := move41PiSourceLocalCarrier_sum h hp
  apply mem_move41PiTargetLocalCarrier_of_coordinates h
  · intro z
    have ha := hnonneg a
    have hb := hnonneg b
    have hc := hnonneg c
    have hd := hnonneg d
    have he := hnonneg e
    simp only [move41PiRadialMap]
    split_ifs <;> positivity
  · simp only [move41PiRadialMap]
    have hab : a ≠ b := by simp_all [List.nodup_cons]
    have hac : a ≠ c := by simp_all [List.nodup_cons]
    have had : a ≠ d := by simp_all [List.nodup_cons]
    have hae : a ≠ e := by simp_all [List.nodup_cons]
    have hbc : b ≠ c := by simp_all [List.nodup_cons]
    have hbd : b ≠ d := by simp_all [List.nodup_cons]
    have hbe : b ≠ e := by simp_all [List.nodup_cons]
    have hcd : c ≠ d := by simp_all [List.nodup_cons]
    have hce : c ≠ e := by simp_all [List.nodup_cons]
    have hde : d ≠ e := by simp_all [List.nodup_cons]
    simp [Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hae,
      Ne.symm hbc, Ne.symm hbd, Ne.symm hbe, Ne.symm hcd,
      Ne.symm hce, Ne.symm hde]
    linarith
  · simp only [move41PiRadialMap]
    have hae : a ≠ e := by simp_all [List.nodup_cons]
    have hbe : b ≠ e := by simp_all [List.nodup_cons]
    have hce : c ≠ e := by simp_all [List.nodup_cons]
    have hde : d ≠ e := by simp_all [List.nodup_cons]
    simp [Ne.symm hae, Ne.symm hbe, Ne.symm hce, Ne.symm hde]
  · intro z hza hzb hzc hzd
    simp [move41PiRadialMap, hza, hzb, hzc, hzd]

/-- The inverse radial barycentric formula on the solid outer tetrahedron.
It subtracts the least outer coordinate and records four times that least
coordinate at the cone point. -/
noncomputable def move41PiRadialInv (a b c d e : Nat) (q : Nat → ℝ) :
    Nat → ℝ :=
  let m := min (min (q a) (q b)) (min (q c) (q d))
  fun z ↦
    if z = a then q a - m
    else if z = b then q b - m
    else if z = c then q c - m
    else if z = d then q d - m
    else if z = e then 4 * m
    else 0

/-- The inverse radial formula carries the solid target tetrahedron into the
cone on its boundary. -/
theorem move41PiRadialInv_mem_source
    {a b c d e : Nat} (h : [a, b, c, d, e].Nodup) {q : Nat → ℝ}
    (hq : q ∈ move41PiTargetLocalCarrier a b c d e) :
    move41PiRadialInv a b c d e q ∈
      move41PiSourceLocalCarrier a b c d e := by
  let m : ℝ := min (min (q a) (q b)) (min (q c) (q d))
  have hnonneg := move41PiTargetLocalCarrier_nonneg hq
  have hsum := move41PiTargetLocalCarrier_sum h hq
  have he := move41PiTargetLocalCarrier_center_eq_zero h hq
  have hma : m ≤ q a := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmb : m ≤ q b := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmc : m ≤ q c := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmd : m ≤ q d := le_trans (min_le_right _ _) (min_le_right _ _)
  have hm0 : 0 ≤ m := le_min (le_min (hnonneg a) (hnonneg b))
    (le_min (hnonneg c) (hnonneg d))
  apply mem_move41PiSourceLocalCarrier_of_coordinates h
  · intro z
    simp only [move41PiRadialInv]
    split_ifs <;> linarith
  · simp only [move41PiRadialInv]
    have hab : a ≠ b := by simp_all [List.nodup_cons]
    have hac : a ≠ c := by simp_all [List.nodup_cons]
    have had : a ≠ d := by simp_all [List.nodup_cons]
    have hae : a ≠ e := by simp_all [List.nodup_cons]
    have hbc : b ≠ c := by simp_all [List.nodup_cons]
    have hbd : b ≠ d := by simp_all [List.nodup_cons]
    have hbe : b ≠ e := by simp_all [List.nodup_cons]
    have hcd : c ≠ d := by simp_all [List.nodup_cons]
    have hce : c ≠ e := by simp_all [List.nodup_cons]
    have hde : d ≠ e := by simp_all [List.nodup_cons]
    simp [Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hae,
      Ne.symm hbc, Ne.symm hbd, Ne.symm hbe, Ne.symm hcd,
      Ne.symm hce, Ne.symm hde]
    linarith
  · simp only [move41PiRadialInv, m]
    rcases min_choice (min (q a) (q b)) (min (q c) (q d)) with hm | hm
    · rcases min_choice (q a) (q b) with hab | hab
      · have hma' : m = q a := hm.trans hab
        have hma'' : min (min (q a) (q b)) (min (q c) (q d)) = q a := hma'
        left
        simp [move41PiRadialInv, hma'']
      · have hmb' : m = q b := hm.trans hab
        have hmb'' : min (min (q a) (q b)) (min (q c) (q d)) = q b := hmb'
        have hba : b ≠ a := by
          exact Ne.symm (by simp_all [List.nodup_cons] : a ≠ b)
        right; left
        simp [move41PiRadialInv, hmb'', hba]
    · rcases min_choice (q c) (q d) with hcd | hcd
      · have hmc' : m = q c := hm.trans hcd
        have hmc'' : min (min (q a) (q b)) (min (q c) (q d)) = q c := hmc'
        have hca : c ≠ a := by
          exact Ne.symm (by simp_all [List.nodup_cons] : a ≠ c)
        have hcb : c ≠ b := by
          exact Ne.symm (by simp_all [List.nodup_cons] : b ≠ c)
        right; right; left
        simp [move41PiRadialInv, hmc'', hca, hcb]
      · have hmd' : m = q d := hm.trans hcd
        have hmd'' : min (min (q a) (q b)) (min (q c) (q d)) = q d := hmd'
        have hda : d ≠ a := by
          exact Ne.symm (by simp_all [List.nodup_cons] : a ≠ d)
        have hdb : d ≠ b := by
          exact Ne.symm (by simp_all [List.nodup_cons] : b ≠ d)
        have hdc : d ≠ c := by
          exact Ne.symm (by simp_all [List.nodup_cons] : c ≠ d)
        right; right; right
        simp [move41PiRadialInv, hmd'', hda, hdb, hdc]
  · intro z hza hzb hzc hzd hze
    simp [move41PiRadialInv, hza, hzb, hzc, hzd, hze]

end Poincare
