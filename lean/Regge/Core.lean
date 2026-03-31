import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Regge

universe u

structure SimplicialComplex where
  V : Type u
  inst : DecidableEq V
  faces : Finset (Finset V)
  edges : Finset (V × V)
  lengths : (V × V) → ℝ

attribute [instance] SimplicialComplex.inst

axiom so3 : Type
axiom TetraGeom : Type
axiom FundamentalGroup : SimplicialComplex → Type

axiom zero_so3 : so3
axiom exp_so3 : so3 → so3
axiom so3_add : so3 → so3 → so3

axiom detG : TetraGeom → ℝ
axiom LocalIndependent : TetraGeom → Prop

axiom det_nonzero_implies_local_rigidity :
  ∀ σ : TetraGeom, detG σ ≠ 0 → LocalIndependent σ

end Regge
