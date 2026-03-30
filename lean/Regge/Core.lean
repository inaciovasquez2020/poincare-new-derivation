namespace Regge

constant zero_so3 : so3
constant exp_so3 : so3 → so3
constant so3_add : so3 → so3 → so3

constant detG : TetraGeom → ℝ
constant LocalIndependent : TetraGeom → Prop

axiom det_nonzero_implies_local_rigidity :
  ∀ σ : TetraGeom, detG σ ≠ 0 → LocalIndependent σ

