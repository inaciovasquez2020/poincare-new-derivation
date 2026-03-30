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

-- Missing SO(3) operations
constant zero_so3 : so3
constant exp_so3 : so3 → so3
constant so3_add : so3 → so3 → so3

-- Missing TetraGeom operations
constant detG : TetraGeom → ℝ
constant LocalIndependent : TetraGeom → Prop

axiom det_nonzero_implies_local_rigidity :
  ∀ σ : TetraGeom, detG σ ≠ 0 → LocalIndependent σ

end Regge
