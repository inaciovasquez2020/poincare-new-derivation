import Poincare.Triangulation

namespace Poincare

inductive PachnerMove where
| move23
| move32
| move14
| move41

axiom applyMove : Triangulation → PachnerMove → Triangulation

axiom selectMove : Triangulation → PachnerMove

end Poincare
