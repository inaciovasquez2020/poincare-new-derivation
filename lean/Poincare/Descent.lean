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

def selectMove (K : Triangulation) : PachnerMove :=
  match pivotVertex K with
  | none => PachnerMove.move23
  | some v =>
      if vertexDegree K v > targetDegree then PachnerMove.move32
      else if vertexDegree K v < targetDegree then PachnerMove.move14
      else PachnerMove.move23

def applyMove (K : Triangulation) (m : PachnerMove) : Triangulation :=
  match K.tets with
  | [] => K
  | t :: ts =>
      match m with
      | PachnerMove.move14 =>
          { tets := (Tet.mk t.v0 t.v1 t.v2 t.v3) :: (Tet.mk t.v0 t.v1 t.v2 (t.v0+1)) :: ts }
      | PachnerMove.move32 =>
          { tets := ts }
      | PachnerMove.move23 =>
          { tets := t :: ts }
      | PachnerMove.move41 =>
          { tets := ts }

def step (K : Triangulation) : Triangulation :=
  applyMove K (selectMove K)

theorem Phi_decreases (K : Triangulation) (h : Phi K > 0) :
  Phi (step K) < Phi K := by
  admit

end Poincare
