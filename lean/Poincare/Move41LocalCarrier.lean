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

end Poincare
