import Regge.Core
import Regge.HolonomyLinearization

namespace Regge

theorem holonomy_completion_stub
  (T : SimplicialComplex)
  (γ : FundamentalGroup T)
  (path : ℝ → (T.V × T.V → ℝ))
  (t : ℝ) :
  ∃ X : so3,
    holonomy_rho T γ path t = exp_so3 X := by
  rcases holonomy_linearization_bound_intealoop T γ path t with ⟨X, _R, hρ, _⟩
  exact ⟨X, hρ⟩

end Regge
