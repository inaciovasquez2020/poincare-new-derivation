import Regge.Core
import Regge.HolonomyLinearization

namespace Regge

theorem local_independent_of_det
  (σ : TetraGeom)
  (h : detG σ ≠ 0) :
  LocalIndependent σ :=
  det_nonzero_implies_local_rigidity σ h

theorem holonomy_completion_stub
  (T : SimplicialComplex)
  (γ : FundamentalGroup T)
  (path : ℝ → (T.V × T.V → ℝ))
  (t : ℝ) :
  ∃ X R : so3,
    holonomy_rho T γ path t = exp_so3 X := by
  rcases holonomy_linearization_bound_intealoop T γ path t with ⟨X, R, hρ, _hbound⟩
  exact ⟨X, R, hρ⟩

theorem holonomy_completion_exists
  (T : SimplicialComplex)
  (γ : FundamentalGroup T)
  (path : ℝ → (T.V × T.V → ℝ))
  (t : ℝ) :
  ∃ X : so3, holonomy_rho T γ path t = exp_so3 X := by
  rcases holonomy_completion_stub T γ path t with ⟨X, _R, hρ⟩
  exact ⟨X, hρ⟩

end Regge
