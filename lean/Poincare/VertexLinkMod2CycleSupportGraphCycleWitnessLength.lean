import Poincare.VertexLinkMod2CycleSupportGraphCycleWitnesses

namespace Poincare

/--
A cycle in the mod-2 support graph has an ordered represented support-edge
witness list whose length is exactly the cycle length, and hence is at least
three.
-/
theorem vertexLinkMod2CycleSupportGraph_isCycle_exists_ordered_support_edge_witnesses_length
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
            p.darts (e :: es) ∧
          (e :: es).length = p.length ∧
          3 ≤ (e :: es).length := by
  rcases
      vertexLinkMod2CycleSupportGraph_isCycle_exists_nonempty_ordered_support_edge_witnesses
        K hcore v f p hp with
    ⟨e, es, hes⟩
  have hlength : p.darts.length = (e :: es).length :=
    hes.length_eq
  have hcycleLength : (e :: es).length = p.length := by
    calc
      (e :: es).length = p.darts.length := hlength.symm
      _ = p.length := SimpleGraph.Walk.length_darts p
  exact ⟨e, es, hes, hcycleLength, hcycleLength ▸ hp.three_le_length⟩

end Poincare
