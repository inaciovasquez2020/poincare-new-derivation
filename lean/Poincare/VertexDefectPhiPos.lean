import Poincare.Triangulation
import Poincare.PhiDecomposition
import Poincare.ZeroDefect

namespace Poincare

theorem vertexDefect_pos_implies_Phi_pos :
  ∀ (T : Triangulation) (v : Nat),
    v ∈ allVerts T →
    vertexDefect T v > 0 →
    Phi T > 0 := by
  intro T v hv hdef
  by_contra hPhi
  have hzero : Phi T = 0 := Nat.eq_zero_of_not_pos hPhi
  have hlocal : delta T v = 0 :=
    (Phi_zero_iff_local_zero T).1 hzero v hv
  exact Nat.ne_of_gt hdef (by simpa [delta] using hlocal)

end Poincare
