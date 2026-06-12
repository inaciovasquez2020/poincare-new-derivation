import Regge.Core

namespace Regge

/--
Minimal distance-squared input surface.

This is only an input-shape lock:
it does not define Regge geometry,
does not prove metric validity,
does not claim Euclidean realizability,
and does not close any DSQ theorem.
-/
structure DSQInputShape where
  EdgeCoord : Type
  dSq : EdgeCoord → ℝ
  is_valid : Prop

def DSQInputShape.HasValidDSQ (S : DSQInputShape) : Prop :=
  S.is_valid

def DSQInputShape.dSq_available (S : DSQInputShape) :
    S.EdgeCoord → ℝ :=
  S.dSq

theorem DSQInputShape.validity_available (S : DSQInputShape) :
    S.HasValidDSQ ↔ S.is_valid := by
  rfl

end Regge
