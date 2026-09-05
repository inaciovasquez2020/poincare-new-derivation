import Poincare.GlobalFanChordEdgeProgress

namespace Poincare

/-- A recurrent high-fan supported-edge state returns to the same unordered
central edge with explicit endpoint identification.  The return may preserve
or reverse the endpoint order. -/
theorem exists_recurrent_highFanEdgeEndpoints
    {K : Triangulation}
    (states : Nat → HighFanState K)
    (hstep :
      ∀ n,
        (states (n + 1)).v = (states n).transition.z0 ∧
        (states (n + 1)).x = (states n).transition.z1)
    (hconsecutive :
      ∀ n,
        (states (n + 1)).edgeState ≠
          (states n).edgeState) :
    ∃ i j,
      i + 1 < j ∧
      j ≤ Fintype.card (SupportedEdgeState K) ∧
      (((states i).v = (states j).v ∧
          (states i).x = (states j).x) ∨
        ((states i).v = (states j).x ∧
          (states i).x = (states j).v)) ∧
      (∀ n,
        i ≤ n →
        n < j →
        (states (n + 1)).v = (states n).transition.z0 ∧
        (states (n + 1)).x = (states n).transition.z1) ∧
      ∀ n,
        i ≤ n →
        n < j →
        (states (n + 1)).edgeState ≠
          (states n).edgeState := by
  obtain ⟨i, j, hgap, hbound, hstate, hsegment, hneq⟩ :=
    exists_recurrent_highFanEdgeState states hstep hconsecutive

  have hkey :
      canonicalEdgeKey (states i).v (states i).x =
        canonicalEdgeKey (states j).v (states j).x := by
    have h :=
      congrArg
        (fun q : SupportedEdgeState K => q.key)
        hstate
    simpa using h

  have hendpoints :
      ((states i).v = (states j).v ∧
          (states i).x = (states j).x) ∨
        ((states i).v = (states j).x ∧
          (states i).x = (states j).v) :=
    (canonicalEdgeKey_eq_iff
      (states i).v
      (states i).x
      (states j).v
      (states j).x
      (states i).endpoints_ne
      (states j).endpoints_ne).1 hkey

  exact ⟨i, j, hgap, hbound, hendpoints, hsegment, hneq⟩

end Poincare
