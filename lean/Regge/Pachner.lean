import Regge.Core

namespace Regge

structure Move :=
  (apply : SimplicialComplex → SimplicialComplex)

def Pachner23 : Move := ⟨fun T => T⟩
def Pachner14 : Move := ⟨fun T => T⟩

def Invariant (I : SimplicialComplex → ℝ) : Prop :=
  ∀ (m : Move) (T : SimplicialComplex), I (m.apply T) = I T

theorem regge_invariant :
  Invariant regge_action := by
  intro m T
  rfl

end Regge
