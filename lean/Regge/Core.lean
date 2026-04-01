import Regge.So3Concrete
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Regge

structure SimplicialComplex where
  V : Type
  inst : DecidableEq V
  faces : Finset (Finset V)
  edges : Finset (V × V)
  lengths : (V × V) → ℝ

attribute [instance] SimplicialComplex.inst

axiom TetraGeom : Type
axiom FundamentalGroup : SimplicialComplex → Type

axiom zero_so3 : so3
axiom exp_so3 : so3 → so3

axiom so3_add : so3 → so3 → so3
axiom so3_neg : so3 → so3
axiom so3_sub : so3 → so3 → so3
axiom so3_bracket : so3 → so3 → so3

axiom detG : TetraGeom → ℝ
axiom LocalIndependent : TetraGeom → Prop

axiom det_nonzero_implies_local_rigidity :
  ∀ σ : TetraGeom, detG σ ≠ 0 → LocalIndependent σ

axiom norm_so3 : so3 → ℝ

axiom norm_nonneg : ∀ X : so3, 0 ≤ norm_so3 X
axiom norm_zero : norm_so3 zero_so3 = 0

axiom norm_add :
  ∀ X Y : so3,
    norm_so3 (so3_add X Y) ≤ norm_so3 X + norm_so3 Y

axiom norm_sub :
  ∀ X Y : so3,
    norm_so3 (so3_sub X Y) ≤ norm_so3 X + norm_so3 Y

axiom norm_bracket_bound :
  ∀ X Y : so3,
    norm_so3 (so3_bracket X Y) ≤ norm_so3 X * norm_so3 Y

end Regge
