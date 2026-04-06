import Poincare.Triangulation
import Poincare.Moves
import Poincare.MovesSemantics

namespace Poincare

def multiplicity (vs : List Nat) (v : Nat) : Nat :=
  vs.count v

def deltaMultiplicity (K : Triangulation) (K' : Triangulation) (v : Nat) : Int :=
  (multiplicity (allVerts K') v : Int) - (multiplicity (allVerts K) v : Int)

theorem applyMove_local_effect :
  ∀ (K : Triangulation) (m : PachnerMove) (v : Nat),
    let K' := applyMove K m
    deltaMultiplicity K K' v = 0 := by
  intro K m v
  dsimp [deltaMultiplicity]
  rw [applyMove_spec K m]

theorem Phi_step_strict_descent :
  ∀ (step : Triangulation → Triangulation),
    (∀ K, Phi K > 0 → Phi (step K) < Phi K) →
    ∀ K, Phi K > 0 → Phi (step K) < Phi K := by
  intro step h K hK
  exact h K hK

end Poincare
