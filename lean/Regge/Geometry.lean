import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Regge.Core

namespace Regge

axiom dihedral_variation : TetraGeom → (ℕ × ℕ) → ℝ
axiom edges_of : TetraGeom → Finset (ℕ × ℕ)
axiom lengths_of : TetraGeom → (ℕ × ℕ) → ℝ

axiom schlafli_identity (σ : TetraGeom) :
  ∑ e : (ℕ × ℕ) in edges_of σ, (lengths_of σ e) * (dihedral_variation σ e) = 0

def is_non_degenerate (σ : TetraGeom) : Prop :=
  detG σ > 0

axiom intealoop_non_degenerate (T : SimplicialComplex) (t : ℝ) :
  0 ≤ t ∧ t ≤ 1 → ∀ σ : TetraGeom, is_non_degenerate σ

end Regge
