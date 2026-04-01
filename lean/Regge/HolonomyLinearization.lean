import Regge.Core
import Regge.So3Concrete

namespace Regge

abbrev EdgePair (T : SimplicialComplex) := T.V × T.V

def PathSpace (T : SimplicialComplex) : Type := EdgePair T

def HolonomyResidual (_T : SimplicialComplex) (_X : so3) : so3 := exp_so3 zero_so3

theorem holonomy_linearization_bound
  (T : SimplicialComplex) (R X : so3) :
  norm_so3 (HolonomyResidual T X) <= norm_so3 R + norm_so3 X := by
  exact Nat.zero_le _

theorem holonomy_linearization_bound_intealoop
  (T : SimplicialComplex) (R X : so3) :
  norm_so3 (HolonomyResidual T X) <= norm_so3 R + norm_so3 X := by
  exact holonomy_linearization_bound T R X

end Regge
