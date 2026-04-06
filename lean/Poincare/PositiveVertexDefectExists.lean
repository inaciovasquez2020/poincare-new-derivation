import Poincare.ZeroDefect

namespace Poincare

theorem positive_vertexDefect_exists
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ v ∈ allVerts K, vertexDefect K v > 0 := by
  classical
  by_contra hno
  have hnonpos : ∀ v ∈ allVerts K, vertexDefect K v ≤ 0 := by
    intro v hv
    by_contra hgt
    exact hno ⟨v, hv, hgt⟩
  have hphi_nonpos : Phi K ≤ 0 := by
    unfold Phi
    induction allVerts K with
    | nil =>
        simp
    | cons v vs ih =>
        have hv0 : vertexDefect K v ≤ 0 := hnonpos v (by simp)
        have hvs0 : ∀ u ∈ vs, vertexDefect K u ≤ 0 := by
          intro u hu
          exact hnonpos u (by simp [hu])
        simp
        exact add_nonpos hv0 (ih hvs0)
  exact not_lt_of_ge hphi_nonpos hPhi

end Poincare
