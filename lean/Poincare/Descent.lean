import Poincare.Triangulation
import Poincare.Moves

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

import Poincare.LocalEffect

theorem Phi_decreases (K : Triangulation) (h : Phi K > 0) :
  Phi (step K) < Phi K :=
  Phi_step_strict_descent K h

end Poincare
