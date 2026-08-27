import Poincare.GlobalFanChordTransition

namespace Poincare

/--
A fan-chord transition cannot return the same unordered supported edge as its
parent edge.  The transition witness contains both output endpoints, while
`escapes_old_edge` certifies that the same witness omits at least one endpoint
of the parent edge.

This is only a one-step nonself statement.  It does not assert termination or
acyclicity of repeated fan-chord continuation.
-/
theorem FanChordTransition.edgeState_ne_parent
    {K : Triangulation}
    {v x : Nat}
    (T : FanChordTransition K v x)
    (hv : v ∈ vertexSupport K)
    (hx : x ∈ vertexSupport K)
    (hvx : v ≠ x) :
    T.edgeState ≠
      supportedEdgeStateOfDistinct K v x hv hx hvx := by
  intro hstate

  have hkey :
      canonicalEdgeKey T.z0 T.z1 =
        canonicalEdgeKey v x := by
    calc
      canonicalEdgeKey T.z0 T.z1 =
          (supportedEdgeStateOfDistinct
            K
            T.z0
            T.z1
            T.z0_supported
            T.z1_supported
            T.endpoints_ne).key :=
        (supportedEdgeStateOfDistinct_key
          K
          T.z0
          T.z1
          T.z0_supported
          T.z1_supported
          T.endpoints_ne).symm

      _ = T.edgeState.key := by
        rw [T.edgeState_eq]

      _ =
          (supportedEdgeStateOfDistinct
            K v x hv hx hvx).key := by
        exact
          congrArg
            (fun q : SupportedEdgeState K => q.key)
            hstate

      _ = canonicalEdgeKey v x := by
        exact
          supportedEdgeStateOfDistinct_key
            K v x hv hx hvx

  rcases
      (canonicalEdgeKey_eq_iff
        T.z0
        T.z1
        v
        x
        T.endpoints_ne
        hvx).1 hkey with
    hsame | hswap

  · rcases hsame with ⟨hz0v, hz1x⟩
    rcases T.escapes_old_edge with hvabs | hxabs

    · apply hvabs
      simpa [hz0v] using T.z0_mem

    · apply hxabs
      simpa [hz1x] using T.z1_mem

  · rcases hswap with ⟨hz0x, hz1v⟩
    rcases T.escapes_old_edge with hvabs | hxabs

    · apply hvabs
      simpa [hz1v] using T.z1_mem

    · apply hxabs
      simpa [hz0x] using T.z0_mem

end Poincare
