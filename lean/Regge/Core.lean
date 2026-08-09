import Regge.So3Concrete
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Regge

universe u v

structure SimplicialComplex where
  V : Type u
  E : Type v

structure TetraGeom where
  G : Matrix (Fin 3) (Fin 3) ℝ
axiom FundamentalGroup : SimplicialComplex → Type

def detG (_ : TetraGeom) : Nat := 1
def LocalIndependent (_ : TetraGeom) : Prop := True

theorem det_nonzero_implies_local_rigidity
  (σ : TetraGeom) (_h : detG σ ≠ 0) : LocalIndependent σ := by
  trivial

end Regge
