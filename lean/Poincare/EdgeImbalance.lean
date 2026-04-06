import Mathlib
import Poincare.Triangulation

namespace Poincare

axiom edge_imbalance_measure : Triangulation → Nat
axiom edge_flip : Triangulation → Nat → Triangulation

theorem positive_edge_imbalance_exists :
  ∀ T : Triangulation,
    edge_imbalance_measure T > 0 →
    ∃ e : Nat, edge_imbalance_measure (edge_flip T e) < edge_imbalance_measure T := by

  sorry

theorem edge_imbalance_conditional :
  ∀ T : Triangulation,
    edge_imbalance_measure T > 0 →
    ∃ T' : Triangulation, edge_imbalance_measure T' < edge_imbalance_measure T := by
  intro T hT
  obtain ⟨e, he⟩ := positive_edge_imbalance_exists T hT
  exact ⟨edge_flip T e, he⟩

end Poincare
