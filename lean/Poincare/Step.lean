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

noncomputable def step (K : Triangulation) : Triangulation :=
applyMove K (selectMove K)

end Poincare
