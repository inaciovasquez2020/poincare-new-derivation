import Mathlib
import Poincare.ZeroDefectCoreGap

namespace Poincare

/-- Vanishing support defect is exactly degree four at every represented vertex. -/
theorem PhiSupport_zero_iff_vertexDegree_eq_four (K : Triangulation) :
    PhiSupport K = 0 ↔
      ∀ v ∈ vertexSupport K, vertexDegree K v = 4 := by
  rw [phiSupport_zero_iff_phi_zero]
  constructor
  · intro hPhi v hv
    have hdef : vertexDefect K v = 0 :=
      phi_sum_zero_implies_supportwise_zero K hPhi v
        ((mem_vertexSupport_iff K v).mp hv)
    unfold vertexDefect targetDegree at hdef
    have hint : (vertexDegree K v : Int) - 4 = 0 :=
      Int.natAbs_eq_zero.mp hdef
    omega
  · intro hdegree
    have hall : ∀ v ∈ allVerts K, vertexDefect K v = 0 := by
      intro v hv
      have hvSupport : v ∈ vertexSupport K :=
        (mem_vertexSupport_iff K v).mpr hv
      unfold vertexDefect targetDegree
      rw [hdegree v hvSupport]
      simp
    have hfold : ∀ vs : List Nat,
        (∀ v ∈ vs, vertexDefect K v = 0) →
          vs.foldl (fun acc v ↦ acc + vertexDefect K v) 0 = 0 := by
      intro vs hvs
      induction vs with
      | nil => rfl
      | cons a tail ih =>
          have ha := hvs a (by simp)
          have htail : ∀ v ∈ tail, vertexDefect K v = 0 := by
            intro v hv
            exact hvs v (by simp [hv])
          simp [ha, ih htail]
    exact hfold (allVerts K) hall

/-- `normalized` carries no more and no less than supportwise degree four. -/
theorem normalized_iff_vertexDegree_eq_four (K : Triangulation) :
    normalized K ↔
      ∀ v ∈ vertexSupport K, vertexDegree K v = 4 := by
  exact PhiSupport_zero_iff_vertexDegree_eq_four K

end Poincare
