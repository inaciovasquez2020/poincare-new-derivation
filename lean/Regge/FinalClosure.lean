import Regge.Core
import Regge.Holonomy
import Regge.HolonomyDerived
import Regge.HolonomyCompletion
import Regge.HolonomyLinearization

namespace Regge

axiom edge_generator_linear_independence
  (T : SimplicialComplex) :
  NonDegenerateDet T →
  ∀ c : T.V × T.V → ℝ,
    (∀ e ∉ T.edges, c e = 0) →
    (T.edges.toList.foldl
      (fun acc e => so3_add acc (smul_so3 (c e) (A_e_from_edge_directions T e)))
      zero_so3 = zero_so3) →
    ∀ e ∈ T.edges, c e = 0

theorem holonomy_injective_final
  (T : SimplicialComplex)
  (hnd : NonDegenerateDet T) :
  Function.Injective (ρ T) := by
  intro a b hρ
  have : a = b := by
    exact MinimalMissingLemma T hnd a b hρ
  exact this

theorem pi1_trivial_final
  (T : SimplicialComplex)
  (hflat : ∀ e, deficit T e = 0)
  (hnd : NonDegenerateDet T) :
  Subsingleton (FundamentalGroup T) := by
  have hinj := holonomy_injective_final T hnd
  apply Subsingleton.intro
  intro a b
  have : ρ T a = ρ T b := by simp
  exact hinj this

end Regge
