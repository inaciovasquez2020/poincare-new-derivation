import Poincare.GlobalMove32WitnessedReentryFreshEndpoints
import Mathlib.Tactic

namespace Poincare

/--
If a witnessed Move32 reentry returns its next shared edge to an anchor edge,
then any endpoint of the predecessor shared edge that lies in the anchor's
five-vertex carrier cannot be one of the anchor shared-edge endpoints.
Consequently that endpoint lies in the anchor source face.
-/
theorem
    ClosedTriangulationCore.witnessedReentry_predecessor_sharedEdge_inside_anchor_sourceFace_of_return_edge
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks : ∀ v ∈ vertexSupport K, VertexLinkConnected K v)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (anchor s t : Move32Site)
    (hsRealized : s.RealizedIn K)
    (hstep : Move32SourceFaceWitnessedReentry K s t)
    (hreturn :
      (t.d = anchor.d ∧ t.e = anchor.e) ∨
      (t.d = anchor.e ∧ t.e = anchor.d))
    (hsdInside :
      s.d ∈ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e]) :
    s.d ∈ [anchor.a, anchor.b, anchor.c] := by
  have hdis :=
    hcore.witnessedReentry_next_sharedEdge_disjoint_previous_carrier_of_no_degree_four
      hlinks hNoFour s t hsRealized hstep

  have hanchorDNot :
      anchor.d ∉ [s.a, s.b, s.c, s.d, s.e] := by
    intro hmem
    have hleft : anchor.d ∈ [t.d, t.e] := by
      rcases hreturn with hdirect | hreverse
      · simpa [hdirect.1]
      · simpa [hreverse.2]
    exact (List.disjoint_left.mp hdis) anchor.d hleft hmem

  have hanchorENot :
      anchor.e ∉ [s.a, s.b, s.c, s.d, s.e] := by
    intro hmem
    have hleft : anchor.e ∈ [t.d, t.e] := by
      rcases hreturn with hdirect | hreverse
      · simpa [hdirect.2]
      · simpa [hreverse.1]
    exact (List.disjoint_left.mp hdis) anchor.e hleft hmem

  have hsdNeD : s.d ≠ anchor.d := by
    intro h
    apply hanchorDNot
    simp [h]

  have hsdNeE : s.d ≠ anchor.e := by
    intro h
    apply hanchorENot
    simp [h]

  simp only [List.mem_cons, List.mem_singleton] at hsdInside ⊢
  rcases hsdInside with ha | hb | hc | hd | he
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hc)
  · exact (hsdNeD hd).elim
  · exact (hsdNeE he).elim

end Poincare
