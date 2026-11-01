import Poincare.StabilizedFinitePathDescent
import Poincare.PerelmanPL

namespace Poincare

/-- Conditional finite-path descent to genuine three-sphere recognition.
The global stabilized descent hypothesis is explicit and is not proved here. -/
theorem stabilizedPathDescent_implies_Perelman_PL
    (hcoverage : SimplyConnectedStabilizedPathDescent) :
    Perelman_PL := by
  exact globalPhiSupportDescent_implies_Perelman_PL
    (stabilizedPathDescent_implies_globalDescent hcoverage)

end Poincare
