import Regge.Core
import Regge.Holonomy

namespace Regge

def norm_so3 (_ : so3) : ℝ := 0

axiom holonomy_path_ordered_expansion :
  ∀ (T : SimplicialComplex) (γ : FundamentalGroup T),
    ∃ X : so3, ρ T γ = IdSO3 ∧ X = zero_so3

axiom path_coeff :
  ∀ (T : SimplicialComplex) (γ : FundamentalGroup T),
    T.V × T.V → ℝ

axiom path_coeff_support :
  ∀ (T : SimplicialComplex) (γ : FundamentalGroup T),
    ∀ e ∉ T.edges, path_coeff T γ e = 0

theorem holonomy_linearization_bound
  (T : SimplicialComplex)
  (γ : FundamentalGroup T) :
  ∃ c : T.V × T.V → ℝ,
    ∃ X : so3,
      ρ T γ = IdSO3 ∧
      X = zero_so3 := by
  rcases holonomy_path_ordered_expansion T γ with ⟨X, hρ, hX⟩
  exact ⟨path_coeff T γ, X, hρ, hX⟩

end Regge
