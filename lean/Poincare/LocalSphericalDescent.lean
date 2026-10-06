import Mathlib
import Poincare.Triangulation
import Poincare.ZeroDefect
import Poincare.PhiDecomposition
import Poincare.MovesImpl
import Poincare.MovesImplGreedySpec
import Poincare.VertexDefectPhiPos

namespace Poincare

def moveAt (T : Triangulation) (_v : Nat) : Triangulation :=
  applyMoveImpl T (selectMoveImplGreedy T)

theorem local_positive_vertex_exists :
  ∀ T : Triangulation,
    Phi T > 0 →
    ∃ v : Nat, v ∈ allVerts T ∧ vertexDefect T v > 0 := by
  intro T hPhi
  classical
  by_contra hnone
  have hzero : ∀ v ∈ allVerts T, delta T v = 0 := by
    intro v hv
    have hnp : ¬ vertexDefect T v > 0 := by
      intro hvpos
      exact hnone ⟨v, hv, hvpos⟩
    have hv0 : vertexDefect T v = 0 := Nat.eq_zero_of_not_pos hnp
    simpa [delta] using hv0
  have hPhi0 : Phi T = 0 := (Phi_zero_iff_local_zero T).2 hzero
  exact Nat.lt_irrefl 0 (hPhi0 ▸ hPhi)

/-
BOUNDARY := ¬ ∀ (T : Triangulation) (v : Nat),
  v ∈ allVerts T →
  vertexDefect T v > 0 →
  Phi (moveAt T v) < Phi T

The definition of moveAt currently uses the identity applyMoveImpl, so this
strict descent statement is not available.

BOUNDARY := ¬ ∀ T : Triangulation,
  Phi T > 0 → ∃ T', Phi T' < Phi T

A genuine legal Pachner move and a proved strict Phi descent are required.
-/

end Poincare
