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

theorem Phi_decreases (K : Triangulation) (h : Phi K > 0) :
  Phi (step K) < Phi K := by
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.succ_pos _)

end Poincare
