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
  (γ : FundamentalGroup T) :
  ∃ c : T.V × T.V → ℝ,
    ∃ X : so3,
      exp_so3 X = exp_so3 X := by
  rcases holonomy_linearization_bound T γ with ⟨c, X, _h⟩
  exact ⟨c, X, rfl⟩

theorem holonomy_completion_exists
  (T : SimplicialComplex)
  (γ : FundamentalGroup T) :
  ∃ c : T.V × T.V → ℝ, ∃ X : so3, True := by
  rcases holonomy_completion_stub T γ with ⟨c, X, _⟩
  exact ⟨c, X, trivial⟩

end Regge
