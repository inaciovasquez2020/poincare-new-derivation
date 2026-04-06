import Poincare.Triangulation

namespace Poincare

inductive PachnerMove where
| move23
| move32
| move14
| move41

-- keep only minimal interface, mark explicitly as primitive layer
axiom applyMove : Triangulation → PachnerMove → Triangulation
axiom selectMove : Triangulation → PachnerMove

end Poincare
