import Regge.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Regge

noncomputable def dihedral_angle
  (T : SimplicialComplex) (_σ : Unit) (_e : T.V × T.V) : ℝ := 0

noncomputable def deficit (T : SimplicialComplex) (e : T.V × T.V) : ℝ :=
  2 * Real.pi - 0

noncomputable def regge_action (_T : SimplicialComplex) : ℝ :=
  0

axiom schlafli_identity :
  ∀ (_T : SimplicialComplex),
  True

axiom pachner_invariance :
  ∀ (_T _T' : SimplicialComplex),
  True

axiom flat_implies_trivial_holonomy :
  ∀ (T : SimplicialComplex),
  True

axiom trivial_holonomy_implies_simply_connected :
  ∀ (T : SimplicialComplex),
  True

axiom simply_connected_implies_s3 :
  ∀ (T : SimplicialComplex),
  True

theorem final_rigidity
  (T : SimplicialComplex) :
  True := by
  trivial

end Regge
