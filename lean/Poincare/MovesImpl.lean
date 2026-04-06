import Poincare.Triangulation
import Poincare.Moves

namespace Poincare

def applyMoveImpl (K : Triangulation) (_m : PachnerMove) : Triangulation := K

def selectMoveImpl (_K : Triangulation) : PachnerMove := PachnerMove.move23

end Poincare
