import Poincare.Triangulation
import Poincare.Moves
import Poincare.Descent

namespace Poincare

lemma applyMove_defect_balance
  (K : Triangulation)
  (v : Nat)
  (hK : pivotVertex K = some v) :
  let K' := step K
  vertexDefect K' v < vertexDefect K v ∧
  ∀ u : Nat, u ≠ v → vertexDefect K' u ≤ vertexDefect K u :=
by
  sorry

lemma Phi_strict_descent_constructive
  (K : Triangulation)
  (h : Phi K > 0) :
  Phi (step K) < Phi K :=
by
  obtain ⟨v, hv⟩ := Option.exists_of_ne_none (by
    cases hpv : pivotVertex K <;> simp [hpv] at h; contradiction)
  have hbal := applyMove_defect_balance K v hv
  sorry

end Poincare
