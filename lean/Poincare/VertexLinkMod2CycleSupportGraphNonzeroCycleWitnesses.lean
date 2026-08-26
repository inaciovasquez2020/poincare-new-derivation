import Poincare.VertexLinkMod2CycleSupportGraphCycleWitnesses

namespace Poincare

/--
A nonzero represented mod-2 one-cycle directly supplies a genuine support-graph
cycle together with a nonempty ordered list of represented support-edge
witnesses aligned with the cycle darts.
-/
theorem vertexLinkMod2CycleSupportGraph_exists_nonempty_ordered_support_edge_witnesses_of_ne_zero
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (hf :
      f ∈ LinearMap.ker
        (vertexLinkMod2BoundaryOne K hcore v))
    (hfne : f ≠ 0) :
    ∃ x : VertexLinkMod2Vertex K v,
      ∃ c :
          (vertexLinkMod2CycleSupportGraph K hcore v f).Walk x x,
        c.IsCycle ∧
          ∃ e : VertexLinkMod2Edge K hcore v,
            ∃ es : List (VertexLinkMod2Edge K hcore v),
              List.Forall₂
                (fun d e =>
                  e ∈ vertexLinkMod2CycleSupportEdges K hcore v f ∧
                  ((d.fst.1 = e.1.lo ∧ d.snd.1 = e.1.hi) ∨
                   (d.snd.1 = e.1.lo ∧ d.fst.1 = e.1.hi)))
                c.darts (e :: es) := by
  rcases
      vertexLinkMod2CycleSupportGraph_exists_cycle_of_ne_zero
        K hcore v f hf hfne with
    ⟨x, c, hc⟩
  rcases
      vertexLinkMod2CycleSupportGraph_isCycle_exists_nonempty_ordered_support_edge_witnesses
        K hcore v f c hc with
    ⟨e, es, hes⟩
  exact ⟨x, c, hc, e, es, hes⟩

end Poincare
