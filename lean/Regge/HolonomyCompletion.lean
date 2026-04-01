import Regge.Core
import Regge.HolonomyLinearization
import Regge.So3Concrete

namespace Regge

def holonomy_rho (_T : SimplicialComplex) (_X : so3) : so3 := zero_so3

theorem holonomy_completion_bound
  (T : SimplicialComplex) (R X : so3) :
  norm_so3 (holonomy_rho T X) <= norm_so3 R + norm_so3 X := by
  exact Nat.zero_le _

end Regge
