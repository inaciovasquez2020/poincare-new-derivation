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

end Poincare
