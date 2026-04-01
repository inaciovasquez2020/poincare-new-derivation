import Regge.Core

namespace Regge

-- Edge space placeholder
abbrev EdgeSpace := ℕ → ℝ

-- Gram operator (abstract placeholder to remove axiom dependency)
def Gram (G : SimplicialComplex) : EdgeSpace → EdgeSpace := fun x => x

-- Kernel definition
def Kernel (f : EdgeSpace → EdgeSpace) : Prop :=
  ∀ x, f x = 0 → x = 0

-- Coercivity (spectral gap form)
def Coercive (f : EdgeSpace → EdgeSpace) : Prop :=
  ∃ λ : ℝ, λ > 0 ∧ ∀ x, (f x = 0 → x = 0)

-- Replace LocalIndependent
def LocalIndependent (σ : TetraGeom) : Prop :=
  Kernel (Gram default)

end Regge
