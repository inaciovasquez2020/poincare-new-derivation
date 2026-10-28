import Mathlib

/-!
# Conditional holonomy cycle exclusion

This file formalizes the logical conditional only. It does NOT construct a
holonomy for the geometric FanReentryModeStep relation, and it does NOT prove
the geometric hypotheses below from manifold assumptions. Those remain the
mathematical obligations.
-/

namespace Poincare.ConditionalHolonomy

universe u v

variable {State : Type u} {G : Type v} [Group G]

/-- Holonomy assigned to a candidate cycle by a future geometric construction. -/
variable (holonomy : State → G)

/-- Conditional frustration: every admissible cycle has nonidentity holonomy.
This is an assumption/interface, not proved by finiteness. -/
def Frustrated (admissible : State → Prop) : Prop :=
  ∀ c, admissible c → holonomy c ≠ 1

/-- Conditional rigidity: every admissible cycle on a regular manifold has
identity holonomy. This too must be proved geometrically for the actual system. -/
def FlatOnRegular (admissible regular : State → Prop) : Prop :=
  ∀ c, admissible c → regular c → holonomy c = 1

/-- The valid conditional theorem: frustration and rigidity are incompatible
with an admissible cycle on a regular state. -/
theorem no_cycle_of_frustration_and_rigidity
    (admissible regular : State → Prop)
    (hFrustrated : Frustrated holonomy admissible)
    (hFlat : FlatOnRegular holonomy admissible regular)
    (c : State) (hc : admissible c) (hr : regular c) :
    False := by
  have hne : holonomy c ≠ 1 := hFrustrated c hc
  have heq : holonomy c = 1 := hFlat c hc hr
  exact hne heq

/-- Separate boundary-failure alternatives. highEdge and degreeFour are
 distinct predicates and are intentionally not conflated. -/
theorem no_cycle_of_failure_bifurcation
    (admissible highEdge degreeFour : State → Prop)
    (hBifurcate : ∀ c, admissible c → highEdge c ∨ degreeFour c)
    (hNoHigh : ∀ c, admissible c → ¬ highEdge c)
    (hNoFour : ∀ c, admissible c → ¬ degreeFour c)
    (c : State) (hc : admissible c) : False := by
  rcases hBifurcate c hc with hh | hf
  · exact hNoHigh c hc hh
  · exact hNoFour c hc hf

/-- Complete conditional package. The premises supply the geometric facts
that still need proving; no premise follows merely from finiteness or a
spherical link. -/
theorem conditional_cycle_exclusion
    (admissible regular highEdge degreeFour : State → Prop)
    (hFrustrated : Frustrated holonomy admissible)
    (hFlat : FlatOnRegular holonomy admissible regular)
    (hRegular : ∀ c, admissible c → regular c)
    (hBifurcate : ∀ c, admissible c → highEdge c ∨ degreeFour c)
    (hNoHigh : ∀ c, admissible c → ¬ highEdge c)
    (hNoFour : ∀ c, admissible c → ¬ degreeFour c)
    (c : State) (hc : admissible c) : False := by
  exact no_cycle_of_frustration_and_rigidity
    holonomy admissible regular hFrustrated hFlat c hc (hRegular c hc)

end Poincare.ConditionalHolonomy
