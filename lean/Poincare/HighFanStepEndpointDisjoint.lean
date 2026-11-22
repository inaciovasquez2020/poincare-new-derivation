import Poincare.GlobalFanChordEdgeProgress

namespace Poincare

theorem highFan_step_endpoint_disjoint
    {K : Triangulation}
    (states : Nat → HighFanState K)
    (hstep : ∀ n,
      (states (n + 1)).v = (states n).transition.z0 ∧
      (states (n + 1)).x = (states n).transition.z1)
    (n : Nat) :
    (states n).v ≠ (states (n + 1)).v ∧
    (states n).v ≠ (states (n + 1)).x ∧
    (states n).x ≠ (states (n + 1)).v ∧
    (states n).x ≠ (states (n + 1)).x := by
  obtain ⟨h0, h1⟩ := hstep n
  rw [h0, h1]
  have hd := (states n).transition.distinct
  simp at hd
  aesop

end Poincare

#print axioms Poincare.highFan_step_endpoint_disjoint
