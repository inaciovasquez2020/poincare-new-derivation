import Regge.Core

namespace Regge

axiom global_gram_lambda_min : SimplicialComplex → ℝ → ℝ

axiom holonomy_rho :
  (T : SimplicialComplex) →
  FundamentalGroup T →
  (ℝ → (T.V × T.V → ℝ)) →
  ℝ →
  so3

axiom kappa : ℝ

axiom gram_spectral_gap (T : SimplicialComplex) (t : ℝ) :
  global_gram_lambda_min T t > 0

axiom holonomy_linearization_bound_intealoop
  (T : SimplicialComplex)
  (γ : FundamentalGroup T)
  (path : ℝ → (T.V × T.V → ℝ))
  (t : ℝ) :
  ∃ X R : so3,
    holonomy_rho T γ path t = exp_so3 X ∧
    norm_so3 R ≤ (kappa / global_gram_lambda_min T t) * (norm_so3 X)^2

end Regge
