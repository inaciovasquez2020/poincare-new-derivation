import Regge.Core

namespace Regge

/-- Minimal geometry layer to unblock build: remove Finset + membership usage -/
noncomputable def dihedral_angle
  (T : SimplicialComplex) (_σ : Unit) (_e : T.V × T.V) : ℝ := 0

/-- DO NOT redeclare deficit (already in Core) -/

end Regge
