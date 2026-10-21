import Poincare.Triangulation
import Poincare.MovesImpl
import Poincare.MovesImplGreedy

namespace Poincare

/--
The current move implementation is the identity, so the claimed strict
descent property is false. This theorem records a concrete counterexample
instead of postulating greedy-selector correctness.
-/
theorem greedy_selector_strict_descent_impossible :
    ¬ (∀ (K : Triangulation),
      Phi K > 0 →
      Phi (applyMoveImpl K (selectMoveImplGreedy K)) < Phi K) := by
  intro h
  let K : Triangulation :=
    { tets := [{ v0 := 0, v1 := 1, v2 := 2, v3 := 3 }] }
  have hPhi : Phi K > 0 := by
    native_decide
  have hbad : Phi K < Phi K := by
    simpa [applyMoveImpl] using h K hPhi
  exact (Nat.lt_irrefl (Phi K)) hbad

end Poincare
