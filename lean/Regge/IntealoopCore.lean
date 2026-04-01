import Regge.Core

namespace Regge

def FlatInterior (_M : SimplicialComplex) : Prop :=
  ∀ σ : TetraGeom, detG σ ≠ 0 → LocalIndependent σ

def ValidPath (M M' : SimplicialComplex) : Prop :=
  Nonempty (FundamentalGroup M) ∧ Nonempty (FundamentalGroup M')

end Regge
