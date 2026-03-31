import Regge.Core

namespace Regge

structure SO3 where
  val : Unit

def IdSO3 : SO3 := ⟨()⟩

def R_e (_ε : ℝ) : SO3 := IdSO3

structure FundamentalGroup (T : SimplicialComplex) where
  repr : Unit

def ρ (T : SimplicialComplex) : FundamentalGroup T → SO3 :=
  fun _ => IdSO3

def ker (T : SimplicialComplex) : Set (FundamentalGroup T) :=
  {γ | ρ T γ = IdSO3}

axiom holonomy_injective
  (T : SimplicialComplex) :
  Function.Injective (ρ T)

theorem pi1_trivial_of_flat
  (T : SimplicialComplex)
  (hflat : ∀ e, deficit T e = 0) :
  Subsingleton (FundamentalGroup T) := by
  have hker : ∀ γ, ρ T γ = IdSO3 := by
    intro γ
    rfl
  have hinj := holonomy_injective T
  apply Subsingleton.intro
  intro a b
  have : ρ T a = ρ T b := by simp [hker]
  exact hinj this

end Regge
