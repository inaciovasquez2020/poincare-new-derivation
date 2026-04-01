import Regge.Core

namespace Regge

def geomBound : Nat := 1

theorem geomBound_nonneg : 0 <= geomBound := by
  decide

theorem geomBound_pos : 0 < geomBound := by
  decide

end Regge
