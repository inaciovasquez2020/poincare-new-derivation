import Poincare.ZeroDefect

namespace Poincare

theorem positive_vertexDefect_exists
  (K : Triangulation)
  (hPhi : Phi K > 0) :
  ∃ v ∈ allVerts K, vertexDefect K v > 0 := by
  classical
  by_contra hno
  have hzero_v : ∀ v ∈ allVerts K, vertexDefect K v = 0 := by
    intro v hv
    exact Nat.eq_zero_of_not_pos (fun hgt => hno ⟨v, hv, hgt⟩)
  have hsum_zero :
      ∀ vs : List Nat,
        (∀ u ∈ vs, vertexDefect K u = 0) →
        vs.foldl (fun acc v => acc + vertexDefect K v) 0 = 0 := by
    intro vs
    induction vs with
    | nil =>
        intro hvs
        simp
    | cons v vs ih =>
        intro hvs
        have hv0 : vertexDefect K v = 0 := hvs v (by simp)
        have hvs0 : ∀ u ∈ vs, vertexDefect K u = 0 := by
          intro u hu
          exact hvs u (by simp [hu])
        simp [hv0, ih hvs0]
  have hPhi0 : Phi K = 0 := by
    unfold Phi
    exact hsum_zero (allVerts K) hzero_v
  exact Nat.lt_irrefl 0 (hPhi0 ▸ hPhi)

end Poincare
