import Regge.Core

namespace Regge

structure Move where
  apply : SimplicialComplex → SimplicialComplex

def Pachner23 : Move := ⟨fun T => T⟩
def Pachner14 : Move := ⟨fun T => T⟩

def Invariant (I : SimplicialComplex → ℝ) : Prop :=
  ∀ (m : Move) (T : SimplicialComplex), I (m.apply T) = I T

axiom regge_invariant :
  Invariant regge_action

end Regge
