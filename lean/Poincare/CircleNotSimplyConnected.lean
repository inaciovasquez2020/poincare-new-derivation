import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Homotopy.Lifting

namespace Poincare

open Real

/-- The unit circle is not simply connected. -/
theorem circle_not_simplyConnected : ¬ SimplyConnectedSpace Circle := by
  intro hsc
  letI : SimplyConnectedSpace Circle := hsc
  letI : LocPathConnectedSpace Circle :=
    (Circle.isCoveringMap_exp.isQuotientMap fun z ↦
      ⟨Complex.arg z, Circle.exp_arg z⟩).locPathConnectedSpace
  letI : SimplyConnectedSpace ℝ := SimplyConnectedSpace.ofContractible ℝ
  let expMap : C(ℝ, Circle) := ⟨Circle.exp, Circle.exp.continuous⟩
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      (ContinuousMap.id Circle) (1 : Circle) (0 : ℝ) (by simp)
  have hcomp : F.comp expMap = ContinuousMap.id ℝ := by
    obtain ⟨G, -, hG_unique⟩ :=
      Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
        expMap (0 : ℝ) (0 : ℝ) (by simp [expMap])
    have hleft : F.comp expMap = G := hG_unique _ (by
      constructor
      · simpa [expMap] using hF0
      · funext t
        simpa [expMap, Function.comp_def] using congrFun hF (Circle.exp t))
    have hright : ContinuousMap.id ℝ = G := hG_unique _ (by
      constructor
      · rfl
      · funext t
        simp [expMap])
    exact hleft.trans hright.symm
  have hperiod : F (Circle.exp (2 * π)) = F (Circle.exp 0) := by simp
  have htwo : F (Circle.exp (2 * π)) = 2 * π := by
    simpa [expMap] using ContinuousMap.congr_fun hcomp (2 * π)
  have hzero : F (Circle.exp 0) = 0 := by
    simpa [expMap] using ContinuousMap.congr_fun hcomp 0
  linarith [Real.pi_pos]

end Poincare
