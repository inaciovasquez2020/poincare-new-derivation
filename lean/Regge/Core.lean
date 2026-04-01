import Regge.So3Concrete
import Mathlib.Data.Real.Defs

namespace Regge

structure SimplicialComplex where
  V : Type
  E : Type

axiom TetraGeom : Type
axiom FundamentalGroup : SimplicialComplex → Type

-- We use (1 : ℝ) to ensure the instance is found
axiom detG : TetraGeom → ℝ
axiom LocalIndependent : TetraGeom → Prop

axiom det_nonzero_implies_local_rigidity :
  ∀ σ : TetraGeom, detG σ ≠ 0 → LocalIndependent σ

end Regge
