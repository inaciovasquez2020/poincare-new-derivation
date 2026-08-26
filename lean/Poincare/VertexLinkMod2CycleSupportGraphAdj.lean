import Poincare.VertexLinkMod2CycleContinuation

namespace Poincare

/--
Adjacency in the finite mod-2 cycle support graph is exactly the presence of
a represented support edge with the two vertices as its canonical endpoints,
in either orientation.
-/
theorem vertexLinkMod2CycleSupportGraph_adj_iff_support_edge
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (x y : VertexLinkMod2Vertex K v) :
    (vertexLinkMod2CycleSupportGraph K hcore v f).Adj x y ↔
      ∃ e : VertexLinkMod2Edge K hcore v,
        e ∈ vertexLinkMod2CycleSupportEdges K hcore v f ∧
        ((x.1 = e.1.lo ∧ y.1 = e.1.hi) ∨
         (y.1 = e.1.lo ∧ x.1 = e.1.hi)) := by
  simp only [
    vertexLinkMod2CycleSupportGraph,
    SimpleGraph.fromRel_adj
  ]
  constructor
  · rintro ⟨_, hxy | hyx⟩
    · rcases hxy with ⟨e, he, hx, hy⟩
      exact ⟨e, he, Or.inl ⟨hx, hy⟩⟩
    · rcases hyx with ⟨e, he, hy, hx⟩
      exact ⟨e, he, Or.inr ⟨hy, hx⟩⟩
  · rintro ⟨e, he, hends⟩
    refine ⟨?_, ?_⟩
    · intro hxy
      have hval : x.1 = y.1 :=
        congrArg (fun z : VertexLinkMod2Vertex K v => z.1) hxy
      rcases hends with hforward | hreverse
      · exact (Nat.ne_of_lt e.1.sorted) (by
          calc
            e.1.lo = x.1 := hforward.1.symm
            _ = y.1 := hval
            _ = e.1.hi := hforward.2)
      · exact (Nat.ne_of_lt e.1.sorted) (by
          calc
            e.1.lo = y.1 := hreverse.1.symm
            _ = x.1 := hval.symm
            _ = e.1.hi := hreverse.2)
    · rcases hends with hforward | hreverse
      · exact Or.inl ⟨e, he, hforward.1, hforward.2⟩
      · exact Or.inr ⟨e, he, hreverse.1, hreverse.2⟩

end Poincare
