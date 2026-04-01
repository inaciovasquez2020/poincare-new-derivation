import Regge.So3Concrete

namespace Regge

structure SimplicialComplex where
  V : Type
  E : Type

structure TetraGeom where
  G : Matrix (Fin 3) (Fin 3) ℝ

def detG (σ : TetraGeom) : ℝ :=
Matrix.det σ.G

def NonDegenerate (σ : TetraGeom) : Prop :=
detG σ ≠ 0

def FlatInterior (_M : SimplicialComplex) : Prop := by
  exact sorry

def ValidPath (_M _M' : SimplicialComplex) : Prop := by
  exact sorry

end Regge
