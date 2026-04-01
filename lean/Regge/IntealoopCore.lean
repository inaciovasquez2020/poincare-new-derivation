import Regge.Core

namespace Regge

def FlatInterior (M : SimplicialComplex) : Prop :=
  ∀ σ : TetraGeom, detG σ ≠ 0 → LocalIndependent σ

def ValidPath (_ _ : SimplicialComplex) : Prop := by
  exact sorry

end Regge
