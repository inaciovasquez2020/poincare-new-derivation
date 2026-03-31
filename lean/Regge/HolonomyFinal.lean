import Regge.Core
import Regge.HolonomyMatrixModel
import Regge.HolonomyRigidity

namespace Regge

theorem holonomy_identity_of_zero
  (T : SimplicialComplex)
  (γ : FundamentalGroup T)
  (path : ℝ → EdgeVec T)
  (t : ℝ)
  (h :
    ∀ X R : so3Model,
      holonomy_product T γ path t = exp_so3_model X →
      so3_norm X = 0) :
  ∃ X : so3Model,
    holonomy_product T γ path t = exp_so3_model X :=
by
  exact holonomy_rigidity_identity T γ path t h

end Regge
