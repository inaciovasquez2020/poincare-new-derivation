namespace Regge

structure SimplicialComplex where
  V : Type
  E : Type

structure TetraGeom where
  G : Unit

def detG (_ : TetraGeom) : ℝ := 1

def NonDegenerate (_ : TetraGeom) : Prop := True

def FlatInterior (_M : SimplicialComplex) : Prop := by
  exact sorry

def ValidPath (_M _M' : SimplicialComplex) : Prop := by
  exact sorry

end Regge
