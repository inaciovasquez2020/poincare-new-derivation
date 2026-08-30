import Poincare.GlobalFanChordTransition

namespace Poincare

/-- A high fan-chord step cannot keep the same unordered central edge.
The transition witness contains both chord endpoints, while by construction it
misses at least one endpoint of the old central edge. -/
theorem FanChordTransition.canonicalEdgeKey_ne_old
    {K : Triangulation} {v x : Nat}
    (T : FanChordTransition K v x)
    (hvx : v ≠ x) :
    canonicalEdgeKey T.z0 T.z1 ≠ canonicalEdgeKey v x := by
  intro hkey
  rcases
      (canonicalEdgeKey_eq_iff
        T.z0 T.z1 v x T.endpoints_ne hvx).1 hkey with
    hdirect | hreverse
  · rcases hdirect with ⟨hz0, hz1⟩
    rcases T.escapes_old_edge with hv | hx
    · apply hv
      simpa [hz0] using T.z0_mem
    · apply hx
      simpa [hz1] using T.z1_mem
  · rcases hreverse with ⟨hz0, hz1⟩
    rcases T.escapes_old_edge with hv | hx
    · apply hv
      simpa [hz1] using T.z1_mem
    · apply hx
      simpa [hz0] using T.z0_mem

end Poincare
