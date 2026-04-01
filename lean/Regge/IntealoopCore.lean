namespace Regge

structure SimplicialComplex where
  V : Type
  E : Type

structure TetraGeom where
  data : Unit

def detG (_ : TetraGeom) : Nat := (1 : Nat)

def NonDegenerate (_ : TetraGeom) : Prop := True

def FlatInterior (_ : SimplicialComplex) : Prop := by
  exact sorry

def ValidPath (_ _ : SimplicialComplex) : Prop := by
  exact sorry

end Regge
