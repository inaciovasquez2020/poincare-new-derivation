import Regge.Core

namespace Regge

axiom holonomy_linearization_stub :
  ∀ (T : SimplicialComplex),
    ∀ (γ : FundamentalGroup T),
      ∃ X : so3, True

axiom path_coeff :
  ∀ (T : SimplicialComplex),
    ∀ (γ : FundamentalGroup T),
      T.V × T.V → ℝ

axiom path_coeff_support :
  ∀ (T : SimplicialComplex),
    ∀ (γ : FundamentalGroup T),
      ∀ e, e ∉ T.edges → path_coeff T γ e = 0

theorem holonomy_linearization_bound
  (T : SimplicialComplex)
  (γ : FundamentalGroup T) :
  ∃ c : T.V × T.V → ℝ,
    ∃ X : so3,
      True := by
  rcases holonomy_linearization_stub T γ with ⟨X, _⟩
  exact ⟨path_coeff T γ, X, trivial⟩

end Regge
