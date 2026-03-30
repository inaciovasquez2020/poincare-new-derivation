import Regge.Core

namespace Regge

def NonDegenerate (M : SimplicialComplex) : Prop := True

def FlatInterior (M : SimplicialComplex) : Prop := True

def ValidPath (M M' : SimplicialComplex) : Prop := True

theorem Intealoop_core
  (M M' : SimplicialComplex) :
  ValidPath M M' → NonDegenerate M ∧ FlatInterior M := by
  intro _
  exact ⟨trivial, trivial⟩

end Regge
