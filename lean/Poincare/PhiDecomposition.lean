import Poincare.Triangulation

namespace Poincare

theorem phi_eq_fold_vertexDefect :
  ∀ K : Triangulation,
    Phi K = (allVerts K).foldl (fun acc v => acc + vertexDefect K v) 0 := by
  intro K
  rfl

theorem vertexDefect_nonneg :
  ∀ K : Triangulation, ∀ v : Nat, 0 ≤ vertexDefect K v := by
  intro K v
  exact Nat.zero_le _

end Poincare
