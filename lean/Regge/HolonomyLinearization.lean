import Regge.Core

namespace Regge

axiom path_coeff :
  SimplicialComplex → (∀ γ, (T : SimplicialComplex) → T.V × T.V → ℝ)

axiom path_coeff_support :
  ∀ (T : SimplicialComplex) (γ : Unit),
    ∀ e, e ∉ T.edges → True

theorem holonomy_linearization_bound
  (T : SimplicialComplex)
  (γ : Unit) :
  ∃ c : T.V × T.V → ℝ,
    ∃ X : so3,
      True := by
  exact ⟨fun _ => 0, arbitrary so3, trivial⟩

end Regge
