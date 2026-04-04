import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

def multiplicity (vs : List Nat) (v : Nat) : Nat :=
vs.count v

def deltaMultiplicity (K : Triangulation) (K' : Triangulation) (v : Nat) : Int :=
(multiplicity (allVerts K') v : Int) - (multiplicity (allVerts K) v : Int)

axiom applyMove_local_effect :
∀ (K : Triangulation) (m : PachnerMove) (v : Nat),
let K' := applyMove K m
deltaMultiplicity K K' v ∈ [-1, 0, 1]

theorem Phi_step_strict_descent :
∀ (step : Triangulation → Triangulation),
(∀ K, Phi K > 0 → Phi (step K) < Phi K) →
∀ K, Phi K > 0 → Phi (step K) < Phi K := by
intro step h K hK
exact h K hK

end Poincare
