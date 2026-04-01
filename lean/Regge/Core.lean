import Regge.So3Concrete

namespace Regge

axiom TetraGeom : Type
axiom SimplicialComplex : Type

axiom FundamentalGroup : SimplicialComplex → Type

axiom detG : TetraGeom → ℝ
axiom LocalIndependent : TetraGeom → Prop

axiom det_nonzero_implies_local_rigidity :
  ∀ σ : TetraGeom, detG σ ≠ 0 → LocalIndependent σ

end Regge
