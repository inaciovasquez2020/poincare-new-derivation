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
    exact le_of_not_gt (fun hgt => hno ⟨v, hv, hgt⟩)
  have hsum_nonpos :
      ∀ vs : List Nat,
        (∀ u ∈ vs, vertexDefect K u ≤ 0) →
        vs.foldl (fun acc v => acc + vertexDefect K v) 0 ≤ 0 := by
    intro vs
    induction vs with
    | nil =>
        intro hvs
        simp
    | cons v vs ih =>
        intro hvs
        have hv0 : vertexDefect K v ≤ 0 := hvs v (by simp)
        have hvs0 : ∀ u ∈ vs, vertexDefect K u ≤ 0 := by
          intro u hu
          exact hvs u (by simp [hu])
        simpa using add_nonpos hv0 (ih hvs0)
  have hphi_nonpos : Phi K ≤ 0 := by
    unfold Phi
    exact hsum_nonpos (allVerts K) hnonpos
  exact not_lt_of_ge hphi_nonpos hPhi

end Poincare
