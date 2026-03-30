import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Regge

structure SimplicialComplex where
  V : Type
  inst : DecidableEq V
  faces : Finset (Finset V)
  edges : Finset (V × V)
  lengths : (V × V) → ℝ

noncomputable def deficit (T : SimplicialComplex) (e : T.V × T.V) : ℝ := 0

end Regge
