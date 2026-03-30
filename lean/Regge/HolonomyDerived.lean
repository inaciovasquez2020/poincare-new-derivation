import Regge.Core
import Regge.Holonomy

namespace Regge

axiom NonDegenerate : SimplicialComplex → Prop

axiom holonomy_injective_derived
  (T : SimplicialComplex) :
  NonDegenerate T ->
  Function.Injective (ρ T)

theorem pi1_trivial_of_flat_nondegenerate
  (T : SimplicialComplex)
  (hflat : ∀ e, deficit T e = 0)
  (hnd : NonDegenerate T) :
  Subsingleton (FundamentalGroup T) := by
  have hker : ∀ γ, ρ T γ = IdSO3 := by
    intro γ
    rfl
  have hinj := holonomy_injective_derived T hnd
  apply Subsingleton.intro
  intro a b
  have hab : ρ T a = ρ T b := by
    simp [hker]
  exact hinj hab

end Regge
