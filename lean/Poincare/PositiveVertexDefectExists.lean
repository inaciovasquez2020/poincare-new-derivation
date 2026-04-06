import Poincare.Defs

namespace Poincare

theorem positive_vertexDefect_exists
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ v ∈ allVerts K, vertexDefect K v > 0 := by
  classical
  by_contra hno
  have hle0 : ∀ v ∈ allVerts K, vertexDefect K v ≤ 0 := by
    intro v hv
    by_contra hgt
    exact hno ⟨v, hv, hgt⟩
  have hzero : Phi K ≤ 0 := by
    unfold Phi
    induction allVerts K with
    | nil =>
        simp
    | cons v vs ih =>
        simp at hle0 ⊢
        have hv : vertexDefect K v ≤ 0 := hle0 v (by simp)
        have hvs : ∀ u ∈ vs, vertexDefect K u ≤ 0 := by
          intro u hu
          exact hle0 u (by simp [hu])
        exact add_nonpos hv (by
          simpa using ih hvs)
  exact not_lt_of_ge hzero hPhi

end Poincare
