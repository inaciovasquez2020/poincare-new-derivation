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

axiom pivotVertex_defect_strict_drop :
  ∀ (K : Triangulation) (h : Phi K > 0),
    ∃ v : Nat,
      pivotVertex K = some v ∧
      vertexDefect (step K) v < vertexDefect K v

axiom nonpivot_vertices_nonincrease :
  ∀ (K : Triangulation) (u : Nat),
    pivotVertex K ≠ some u →
    vertexDefect (step K) u ≤ vertexDefect K u

axiom Phi_step_strict_descent :
  ∀ K : Triangulation,
    Phi K > 0 →
    Phi (step K) < Phi K

end Poincare
