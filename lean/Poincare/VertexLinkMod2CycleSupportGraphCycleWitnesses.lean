import Poincare.VertexLinkMod2CycleSupportGraphWalkWitnesses

namespace Poincare

/--
A cycle in the mod-2 support graph has a nonempty ordered list of represented
support-edge witnesses aligned with its walk darts.
-/
theorem vertexLinkMod2CycleSupportGraph_isCycle_exists_nonempty_ordered_support_edge_witnesses
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    {x : VertexLinkMod2Vertex K v}
    (p : (vertexLinkMod2CycleSupportGraph K hcore v f).Walk x x)
    (hp : p.IsCycle) :
    ∃ e : VertexLinkMod2Edge K hcore v,
      ∃ es : List (VertexLinkMod2Edge K hcore v),
        List.Forall₂
          (fun d e =>
            e ∈ vertexLinkMod2CycleSupportEdges K hcore v f ∧
            ((d.fst.1 = e.1.lo ∧ d.snd.1 = e.1.hi) ∨
             (d.snd.1 = e.1.lo ∧ d.fst.1 = e.1.hi)))
          p.darts (e :: es) := by
  cases p with
  | nil =>
      simp at hp
  | cons h p =>
      rcases
          vertexLinkMod2CycleSupportGraph_walk_exists_ordered_support_edge_witnesses
            K hcore v f (.cons h p) with
        ⟨es, hes⟩
      cases es with
      | nil =>
          cases hes
      | cons e es =>
          exact ⟨e, es, hes⟩

end Poincare
