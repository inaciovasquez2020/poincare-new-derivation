import Poincare.GlobalFanChordRecurrentEdgeEndpoints

namespace Poincare

/-- Under the fail-closed exclusion of legal `2-3` moves, strict topological
`PhiSupport` descent, and the source-obstruction high-edge alternative, every
initial high-fan state produces a finite nonconsecutive recurrent cycle of
central edges.  The return is explicit at the level of the unordered endpoint
pair, and every transition along the recurrent segment is retained.

This theorem is only a finite reduction of the perpetual high-fan branch.  It
does not assert that the recurrent edge cycle is impossible. -/
theorem
    ClosedTriangulationCore.exists_finite_recurrent_highFanEdgeCycle_of_noMove23_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (hNoMove23 :
      ¬ ∃ m : Move23Site,
        m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ p q sigma,
          p ≠ q ∧
          sigma ∈ K.tets ∧
          p ∈ sigma.verts ∧
          q ∈ sigma.verts ∧
          ¬ ((p = s.d ∧ q = s.e) ∨
             (p = s.e ∧ q = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (p ∈ gamma.verts ∧
                   q ∈ gamma.verts))).length)
    (start : HighFanState K) :
    ∃ states : Nat → HighFanState K,
      states 0 = start ∧
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
  obtain ⟨states, hzero, hstep, hconsecutive⟩ :=
    hcore.exists_perpetual_highFanState_of_noMove23_noDescent_noHigh
      hM hlinks hNoFour hNoMove23 hNoDescent hNoHigh start

  obtain ⟨i, j, hgap, hbound, hreturn, hsegment, hneq⟩ :=
    exists_recurrent_highFanEdgeEndpoints states hstep hconsecutive

  exact
    ⟨states, hzero, i, j, hgap, hbound,
      hreturn, hsegment, hneq⟩

end Poincare
