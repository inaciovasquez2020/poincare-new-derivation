import Poincare.Triangulation
import Poincare.PhiDecomposition

namespace Poincare

theorem vertexDefect_pos_implies_Phi_pos
  (T : Triangulation) (v : Nat)
  (hv : v ∈ allVerts T)
  (hpos : vertexDefect T v > 0) :
  Phi T > 0 := by
  classical
  have hsum :
    Phi T =
      vertexDefect T v +
      (List.erase (allVerts T) v).foldl
        (fun acc w => acc + vertexDefect T w) 0 := by
    -- use permutation decomposition instead of dependent pattern matching
    have := List.exists_erase_eq (by simpa using hv)
    rcases this with ⟨l, hl⟩
    subst hl
    simp [phi_eq_fold_vertexDefect, List.foldl_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

  have hrest :
    0 ≤
      (List.erase (allVerts T) v).foldl
        (fun acc w => acc + vertexDefect T w) 0 := by
    apply Nat.zero_le

  have : Phi T ≥ vertexDefect T v := by
    simpa [hsum] using Nat.le_add_right _ _

  exact Nat.lt_of_lt_of_le hpos this

end Poincare
