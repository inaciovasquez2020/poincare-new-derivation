import Poincare.Triangulation

namespace Poincare

inductive PachnerMove where
| move23
| move32
| move14
| move41

def applyMove (K : Triangulation) (_ : PachnerMove) : Triangulation :=
  K

def selectMove (_ : Triangulation) : PachnerMove :=
  PachnerMove.move23

end Poincare
