import Regge.So3Concrete
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Data.Real.Basic

namespace Regge

universe u v

structure SimplicialComplex where
  V : Type u
  E : Type v

structure TetraGeom where
  G : Matrix (Fin 3) (Fin 3) ℝ
axiom FundamentalGroup : SimplicialComplex → Type

def detG (σ : TetraGeom) : ℝ :=
  Matrix.det σ.G
def LocalIndependent (σ : TetraGeom) : Prop :=
  ∀ v : Fin 3 → ℝ, Matrix.mulVec σ.G v = 0 → v = 0

theorem det_nonzero_implies_local_rigidity
  (σ : TetraGeom) (h : detG σ ≠ 0) : LocalIndependent σ := by
  intro v hv
  exact Matrix.eq_zero_of_mulVec_eq_zero
    (M := σ.G) (by simpa [detG] using h) hv

end Regge
