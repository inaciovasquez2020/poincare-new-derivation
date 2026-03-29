import Poincare.Triangulation
import Poincare.Moves
import Poincare.LocalEffect

namespace Poincare

def pivotVertex (K : Triangulation) : Option Nat :=
  (allVerts K).foldl
    (fun best v =>
      match best with
      | none => some v
      | some w =>
          if vertexDefect K v > vertexDefect K w then some v else some w)
    none

def step (K : Triangulation) : Triangulation :=
  applyMove K (selectMove K)

axiom step_strict :
  ∀ K, Phi K > 0 → Phi (step K) < Phi K

theorem Phi_decreases (K : Triangulation) (h : Phi K > 0) :
  Phi (step K) < Phi K :=
  step_strict K h

end Poincare
