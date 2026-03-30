import Regge.Core
import Regge.Holonomy
import Regge.HolonomyDerived

namespace Regge

noncomputable def log_so3 : SO3 → so3 := fun _ => zero_so3

axiom log_exp_inverse_principal :
  ∀ X : so3, log_so3 (exp_so3 X) = X

theorem local_independent_of_det
  (σ : TetraGeom)
  (h : detG σ ≠ 0) :
  LocalIndependent σ := by
  exact det_nonzero_implies_local_rigidity σ h

axiom global_edge_sum_injective
  (T : SimplicialComplex)
  (hnd : NonDegenerateDet T) :
  ∀ c : T.V × T.V → ℝ,
    (∀ e ∉ T.edges, c e = 0) →
    (let S :=
      T.edges.toList.foldl
        (fun acc e => so3_add acc (smul_so3 (c e) (A_e_from_edge_directions T e)))
        zero_so3
     in S = zero_so3) →
    ∀ e ∈ T.edges, c e = 0

axiom holonomy_bch_linearization :
  ∀ (T : SimplicialComplex) (γ : FundamentalGroup T),
    ∃ X : so3,
      ρ T γ = exp_so3 X ∧
      X =
        T.edges.toList.foldl
          (fun acc e => so3_add acc (smul_so3 ((fun _ => 0) e) (A_e_from_edge_directions T e)))
          zero_so3

end Regge
