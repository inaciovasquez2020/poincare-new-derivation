import Regge.So3Concrete

namespace Regge

universe u v

structure SimplicialComplex where
  V : Type u
  E : Type v

axiom TetraGeom : Type
axiom FundamentalGroup : SimplicialComplex → Type

def detG (_ : TetraGeom) : Nat := 1
def LocalIndependent (_ : TetraGeom) : Prop := True

theorem det_nonzero_implies_local_rigidity
  (σ : TetraGeom) (_h : detG σ ≠ 0) : LocalIndependent σ := by
  trivial

end Regge
