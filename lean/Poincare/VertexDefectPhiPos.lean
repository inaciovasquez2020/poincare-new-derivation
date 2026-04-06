import Poincare.Triangulation
import Poincare.PhiDecomposition

namespace Poincare

theorem vertexDefect_pos_implies_Phi_pos
  (T : Triangulation) (v : Nat)
  (hv : v ∈ allVerts T)
  (hpos : vertexDefect T v > 0) :
  Phi T > 0 := by
  rw [phi_eq_fold_vertexDefect]
  induction allVerts T with
  | nil =>
      cases hv
  | cons u us ih =>
      simp at hv ⊢
      rcases hv with rfl | hv'
      · exact Nat.lt_of_lt_of_le hpos (Nat.le_add_right _ _)
      · have hus : us.foldl (fun acc w => acc + vertexDefect T w) 0 > 0 := ih hv' hpos
        exact Nat.lt_of_lt_of_le hus (Nat.le_add_left _ _)

end Poincare
