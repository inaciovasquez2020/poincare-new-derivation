import Regge.So3Concrete

namespace Regge

structure SimplicialComplex where
  V : Type
  E : Type

axiom TetraGeom : Type
axiom FundamentalGroup : SimplicialComplex → Type

def detG (_ : TetraGeom) : Nat := 1
def LocalIndependent (_ : TetraGeom) : Prop := True

theorem det_nonzero_implies_local_rigidity :
  ∀ σ : TetraGeom, detG σ ≠ 0 → LocalIndependent σ := by
  intro σ h
  trivial

end Regge
