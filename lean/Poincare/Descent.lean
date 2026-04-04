import Poincare.Triangulation
import Poincare.Moves
import Poincare.LocalEffect
import Poincare.ExistsStrictDescentMove

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

theorem step_strict :
∀ K, Phi K > 0 → Phi (step K) < Phi K := by
intro K hK
simpa [step] using (exists_strict_descent_move K (Nat.ne_of_gt hK)).choose_spec

theorem Phi_decreases (K : Triangulation) (h : Phi K > 0) :
Phi (step K) < Phi K :=
step_strict K h

end Poincare
