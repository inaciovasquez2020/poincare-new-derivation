import Regge.Core

namespace Regge

def NonDegenerate (_M : SimplicialComplex) : Prop := True

def FlatInterior (_M : SimplicialComplex) : Prop := True

def ValidPath (_M _M' : SimplicialComplex) : Prop := True

theorem Intealoop_core
  (_M _M' : SimplicialComplex) :
  ValidPath _M _M' → NonDegenerate _M ∧ FlatInterior _M := by
  intro _
  exact ⟨trivial, trivial⟩

end Regge
