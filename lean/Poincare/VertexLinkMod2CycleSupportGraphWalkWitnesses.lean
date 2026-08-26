import Poincare.VertexLinkMod2CycleSupportGraphAdj

namespace Poincare

/--
Every step of a walk in the mod-2 cycle support graph has a represented
support-edge witness, and the witnesses can be chosen in the same order as
the walk darts.
-/
theorem vertexLinkMod2CycleSupportGraph_walk_exists_ordered_support_edge_witnesses
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    {x y : VertexLinkMod2Vertex K v}
    (p : (vertexLinkMod2CycleSupportGraph K hcore v f).Walk x y) :
    ∃ es : List (VertexLinkMod2Edge K hcore v),
      List.Forall₂
        (fun d e =>
          e ∈ vertexLinkMod2CycleSupportEdges K hcore v f ∧
          ((d.fst.1 = e.1.lo ∧ d.snd.1 = e.1.hi) ∨
           (d.snd.1 = e.1.lo ∧ d.fst.1 = e.1.hi)))
        p.darts es := by
  induction p with
  | nil =>
      exact ⟨[], .nil⟩
  | cons h p ih =>
      rcases
          (vertexLinkMod2CycleSupportGraph_adj_iff_support_edge
            K hcore v f _ _).1 h with
        ⟨e, he, hends⟩
      rcases ih with ⟨es, hes⟩
      refine ⟨e :: es, ?_⟩
      exact .cons ⟨he, hends⟩ hes

end Poincare
