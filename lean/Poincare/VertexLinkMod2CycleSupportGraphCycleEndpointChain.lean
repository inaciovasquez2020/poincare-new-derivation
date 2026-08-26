import Poincare.VertexLinkMod2CycleSupportGraphCycleWitnessLength

namespace Poincare

/--
The ordered represented support-edge witnesses of a support-graph cycle form
an endpoint chain along the walk: consecutive witnesses contain the exact
walk vertex where the corresponding darts meet, and the last/first witnesses
both contain the cycle base vertex.
-/
theorem vertexLinkMod2CycleSupportGraph_isCycle_exists_ordered_support_edge_endpoint_chain
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
          3 ≤ (e :: es).length ∧
          (∀ i
              (hiD : i + 1 < p.darts.length)
              (hiE : i + 1 < (e :: es).length),
            p.darts[i].snd.1 = p.darts[i + 1].fst.1 ∧
            (p.darts[i].snd.1 = (e :: es)[i].1.lo ∨
             p.darts[i].snd.1 = (e :: es)[i].1.hi) ∧
            (p.darts[i].snd.1 = (e :: es)[i + 1].1.lo ∨
             p.darts[i].snd.1 = (e :: es)[i + 1].1.hi)) ∧
          ((x.1 = ((e :: es).getLast (by simp)).1.lo ∨
            x.1 = ((e :: es).getLast (by simp)).1.hi) ∧
           (x.1 = e.1.lo ∨ x.1 = e.1.hi)) := by
  rcases
      vertexLinkMod2CycleSupportGraph_isCycle_exists_ordered_support_edge_witnesses_length
        K hcore v f p hp with
    ⟨e, es, hes, hlength, hthree⟩
  have hdartsLength : p.darts.length = (e :: es).length :=
    hes.length_eq
  have hchainDarts := SimpleGraph.Walk.isChain_dartAdj_darts p
  have hconsecutive :
      ∀ i
          (hiD : i + 1 < p.darts.length)
          (hiE : i + 1 < (e :: es).length),
        p.darts[i].snd.1 = p.darts[i + 1].fst.1 ∧
        (p.darts[i].snd.1 = (e :: es)[i].1.lo ∨
         p.darts[i].snd.1 = (e :: es)[i].1.hi) ∧
        (p.darts[i].snd.1 = (e :: es)[i + 1].1.lo ∨
         p.darts[i].snd.1 = (e :: es)[i + 1].1.hi) := by
    intro i hiD hiE
    have hi0D : i < p.darts.length := by
      omega
    have hi0E : i < (e :: es).length := by
      omega
    have hdadj :=
      List.IsChain.getElem hchainDarts i hiD
    have hmeet : p.darts[i].snd.1 = p.darts[i + 1].fst.1 :=
      congrArg (fun z : VertexLinkMod2Vertex K v => z.1) hdadj
    have hwi := List.Forall₂.get hes hi0D hi0E
    have hwj := List.Forall₂.get hes hiD hiE
    rcases hwi with ⟨_, hendi⟩
    rcases hwj with ⟨_, hendj⟩
    have hiEndpoint :
        p.darts[i].snd.1 = (e :: es)[i].1.lo ∨
        p.darts[i].snd.1 = (e :: es)[i].1.hi := by
      rcases hendi with hforward | hreverse
      · exact Or.inr hforward.2
      · exact Or.inl hreverse.1
    have hjEndpoint :
        p.darts[i].snd.1 = (e :: es)[i + 1].1.lo ∨
        p.darts[i].snd.1 = (e :: es)[i + 1].1.hi := by
      rcases hendj with hforward | hreverse
      · exact Or.inl (hmeet.trans hforward.1)
      · exact Or.inr (hmeet.trans hreverse.2)
    exact ⟨hmeet, hiEndpoint, hjEndpoint⟩
  have hzeroD : 0 < p.darts.length := by
    omega
  have hzeroE : 0 < (e :: es).length := by
    simp
  have hfirst := hes.get hzeroD hzeroE
  rcases hfirst with ⟨_, hfirstEnds⟩
  have hfirstFst : p.darts[0].fst = x := by
    cases p with
    | nil => simp at hzeroD
    | cons h p => rfl
  have hfirstEndpoint : x.1 = e.1.lo ∨ x.1 = e.1.hi := by
    rcases hfirstEnds with hforward | hreverse
    · exact Or.inl ((congrArg (fun z : VertexLinkMod2Vertex K v => z.1) hfirstFst).symm.trans hforward.1)
    · exact Or.inr ((congrArg (fun z : VertexLinkMod2Vertex K v => z.1) hfirstFst).symm.trans hreverse.2)
  let n := (e :: es).length - 1
  have hnE : n < (e :: es).length := by
    dsimp [n]
    omega
  have hnD : n < p.darts.length := by
    omega
  have hlast := hes.get hnD hnE
  rcases hlast with ⟨_, hlastEnds⟩
  have hlastSnd : p.darts[n].snd = x := by
    dsimp [n]
    grind [SimpleGraph.Walk.snd_darts_getElem]
  have hlastEndpoint :
      x.1 = ((e :: es).getLast (by simp)).1.lo ∨
      x.1 = ((e :: es).getLast (by simp)).1.hi := by
    have hnGetLast : (e :: es)[n] = (e :: es).getLast (by simp) := by
      dsimp [n]
      simpa using List.getElem_length_sub_one (e :: es)
    rcases hlastEnds with hforward | hreverse
    · right
      rw [← hnGetLast]
      exact (congrArg (fun z : VertexLinkMod2Vertex K v => z.1) hlastSnd).symm.trans hforward.2
    · left
      rw [← hnGetLast]
      exact (congrArg (fun z : VertexLinkMod2Vertex K v => z.1) hlastSnd).symm.trans hreverse.1
  exact ⟨e, es, hes, hthree, hconsecutive, hlastEndpoint, hfirstEndpoint⟩

end Poincare