import Mathlib.Tactic

namespace Poincare

/--
A finite set of at least two components, each having a positive number of
crossings, cannot have total crossing number three without some component
having exactly one crossing.

This is the finite counting implication. Its application to the complement
of a vertex-link star separately requires a proof that the component
crossing counts are positive and sum to the three perimeter edges.
-/
theorem exists_component_with_one_crossing_of_total_three
    {ι : Type*} [DecidableEq ι]
    (components : Finset ι)
    (crossingCount : ι → Nat)
    (hcomponents : 2 ≤ components.card)
    (hpositive : ∀ c ∈ components, 0 < crossingCount c)
    (htotal : (∑ c ∈ components, crossingCount c) = 3) :
    ∃ c ∈ components, crossingCount c = 1 := by
  classical
  by_contra hnone
  have htwo : ∀ c ∈ components, 2 ≤ crossingCount c := by
    intro c hc
    have hp := hpositive c hc
    have hne : crossingCount c ≠ 1 := by
      intro heq
      exact hnone ⟨c, hc, heq⟩
    omega
  have hbound :
      (∑ c ∈ components, (2 : Nat)) ≤
        (∑ c ∈ components, crossingCount c) := by
    apply Finset.sum_le_sum
    intro c hc
    exact htwo c hc
  have hsumTwo :
      (∑ c ∈ components, (2 : Nat)) = components.card * 2 := by
    simp
  omega

end Poincare
