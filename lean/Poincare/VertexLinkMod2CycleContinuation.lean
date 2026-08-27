import Poincare.VertexLinkMod2CycleSupport
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Poincare

/--
The finite support edges incident to one represented link vertex.
-/
def vertexLinkMod2CycleIncidentSupportEdges
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (x : VertexLinkMod2Vertex K v) :
    Finset (VertexLinkMod2Edge K hcore v) :=
  (vertexLinkMod2CycleSupportEdges K hcore v f).filter
    fun e => x.1 = e.1.lo ∨ x.1 = e.1.hi

@[simp]
theorem mem_vertexLinkMod2CycleIncidentSupportEdges_iff
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (x : VertexLinkMod2Vertex K v)
    (e : VertexLinkMod2Edge K hcore v) :
    e ∈ vertexLinkMod2CycleIncidentSupportEdges
        K hcore v f x ↔
      f e ≠ 0 ∧
        (x.1 = e.1.lo ∨ x.1 = e.1.hi) := by
  simp [
    vertexLinkMod2CycleIncidentSupportEdges,
    vertexLinkMod2CycleSupportEdges
  ]

theorem card_vertexLinkMod2CycleIncidentSupportEdges
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (x : VertexLinkMod2Vertex K v) :
    (vertexLinkMod2CycleIncidentSupportEdges
      K hcore v f x).card =
      vertexLinkMod2CycleSupportDegree
        K hcore v f x := by
  rfl

/--
Canonical represented vertex corresponding to the low endpoint of a
represented link edge.
-/
def vertexLinkMod2EdgeLoVertex
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : VertexLinkMod2Edge K hcore v) :
    VertexLinkMod2Vertex K v :=
  ⟨e.1.lo, by
    have heList :
        e.1 ∈ vertexLinkEdges K hcore v := by
      simpa only [List.mem_toFinset] using e.2
    have hloList :
        e.1.lo ∈ vertexLinkVertices K v :=
      (vertexLinkRepresentedEdge_has_canonical_endpoints
        K hcore v e.1 heList).1
    simpa only [List.mem_toFinset] using hloList⟩

/--
Canonical represented vertex corresponding to the high endpoint of a
represented link edge.
-/
def vertexLinkMod2EdgeHiVertex
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : VertexLinkMod2Edge K hcore v) :
    VertexLinkMod2Vertex K v :=
  ⟨e.1.hi, by
    have heList :
        e.1 ∈ vertexLinkEdges K hcore v := by
      simpa only [List.mem_toFinset] using e.2
    have hhiList :
        e.1.hi ∈ vertexLinkVertices K v :=
      (vertexLinkRepresentedEdge_has_canonical_endpoints
        K hcore v e.1 heList).2.1
    simpa only [List.mem_toFinset] using hhiList⟩

@[simp]
theorem vertexLinkMod2EdgeLoVertex_val
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : VertexLinkMod2Edge K hcore v) :
    (vertexLinkMod2EdgeLoVertex K hcore v e).1 =
      e.1.lo := by
  rfl

@[simp]
theorem vertexLinkMod2EdgeHiVertex_val
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (e : VertexLinkMod2Edge K hcore v) :
    (vertexLinkMod2EdgeHiVertex K hcore v e).1 =
      e.1.hi := by
  rfl

/--
If a support edge of a mod-2 one-cycle is incident to a represented vertex,
then some different support edge is incident to that same vertex.

This is the exact local continuation property needed to construct a finite
closed edge walk.
-/
theorem vertexLinkMod2Cycle_exists_distinct_incident_support_edge
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (hf :
      f ∈ LinearMap.ker
        (vertexLinkMod2BoundaryOne K hcore v))
    (x : VertexLinkMod2Vertex K v)
    (e : VertexLinkMod2Edge K hcore v)
    (he :
      e ∈ vertexLinkMod2CycleSupportEdges
        K hcore v f)
    (hxe :
      x.1 = e.1.lo ∨ x.1 = e.1.hi) :
    ∃ e' : VertexLinkMod2Edge K hcore v,
      e' ∈ vertexLinkMod2CycleSupportEdges
        K hcore v f ∧
      e' ≠ e ∧
      (x.1 = e'.1.lo ∨ x.1 = e'.1.hi) := by
  let S :=
    vertexLinkMod2CycleIncidentSupportEdges
      K hcore v f x

  have hene :
      f e ≠ 0 :=
    (mem_vertexLinkMod2CycleSupportEdges_iff
      K hcore v f e).1 he

  have heS :
      e ∈ S := by
    simp [S, hene, hxe]

  have hpos :
      0 < S.card :=
    Finset.card_pos.mpr ⟨e, heS⟩

  have heven :
      Even S.card := by
    simpa [
      S,
      vertexLinkMod2CycleIncidentSupportEdges,
      vertexLinkMod2CycleSupportDegree
    ] using
      vertexLinkMod2CycleSupportDegree_even
        K hcore v f hf x

  have htwo :
      1 < S.card := by
    rcases heven with ⟨k, hk⟩
    omega

  rcases Finset.exists_mem_ne htwo e with
    ⟨e', he'S, hne⟩

  have he' :
      e' ∈ vertexLinkMod2CycleSupportEdges
        K hcore v f ∧
      (x.1 = e'.1.lo ∨ x.1 = e'.1.hi) := by
    simpa [S] using he'S

  exact
    ⟨e', he'.1, hne, he'.2⟩

/--
A support cycle can continue through the low endpoint of any current
support edge using a distinct support edge.
-/
theorem vertexLinkMod2Cycle_exists_successor_at_lo
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (hf :
      f ∈ LinearMap.ker
        (vertexLinkMod2BoundaryOne K hcore v))
    (e : VertexLinkMod2Edge K hcore v)
    (he :
      e ∈ vertexLinkMod2CycleSupportEdges
        K hcore v f) :
    ∃ e' : VertexLinkMod2Edge K hcore v,
      e' ∈ vertexLinkMod2CycleSupportEdges
        K hcore v f ∧
      e' ≠ e ∧
      ((vertexLinkMod2EdgeLoVertex
          K hcore v e).1 = e'.1.lo ∨
       (vertexLinkMod2EdgeLoVertex
          K hcore v e).1 = e'.1.hi) := by
  apply
    vertexLinkMod2Cycle_exists_distinct_incident_support_edge
      K hcore v f hf
      (vertexLinkMod2EdgeLoVertex K hcore v e)
      e he
  left
  rfl

/--
A support cycle can continue through the high endpoint of any current
support edge using a distinct support edge.
-/
theorem vertexLinkMod2Cycle_exists_successor_at_hi
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (hf :
      f ∈ LinearMap.ker
        (vertexLinkMod2BoundaryOne K hcore v))
    (e : VertexLinkMod2Edge K hcore v)
    (he :
      e ∈ vertexLinkMod2CycleSupportEdges
        K hcore v f) :
    ∃ e' : VertexLinkMod2Edge K hcore v,
      e' ∈ vertexLinkMod2CycleSupportEdges
        K hcore v f ∧
      e' ≠ e ∧
      ((vertexLinkMod2EdgeHiVertex
          K hcore v e).1 = e'.1.lo ∨
       (vertexLinkMod2EdgeHiVertex
          K hcore v e).1 = e'.1.hi) := by
  apply
    vertexLinkMod2Cycle_exists_distinct_incident_support_edge
      K hcore v f hf
      (vertexLinkMod2EdgeHiVertex K hcore v e)
      e he
  right
  rfl

/--
The finite simple graph carried by the nonzero edges of a represented mod-2
one-cycle. Its vertices are represented link vertices; a support edge joins
its canonical low and high endpoints.
-/
def vertexLinkMod2CycleSupportGraph
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2) :
    SimpleGraph (VertexLinkMod2Vertex K v) :=
  SimpleGraph.fromRel fun x y =>
    ∃ e : VertexLinkMod2Edge K hcore v,
      e ∈ vertexLinkMod2CycleSupportEdges K hcore v f ∧
      x.1 = e.1.lo ∧
      y.1 = e.1.hi

/--
A nonzero represented mod-2 one-cycle has a genuine cycle in its finite
support graph.
-/
theorem vertexLinkMod2CycleSupportGraph_exists_cycle_of_ne_zero
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
          (vertexLinkMod2CycleSupportGraph
            K hcore v f).Walk x x,
        c.IsCycle := by
  classical

  let G :=
    vertexLinkMod2CycleSupportGraph K hcore v f

  change ∃ x : VertexLinkMod2Vertex K v,
    ∃ c : G.Walk x x, c.IsCycle

  have hcoeff :
      ∃ e : VertexLinkMod2Edge K hcore v,
        f e ≠ 0 := by
    by_contra h
    apply hfne
    funext e
    exact not_ne_iff.mp ((not_exists.mp h) e)

  rcases hcoeff with ⟨e₀, he₀ne⟩

  have he₀ :
      e₀ ∈ vertexLinkMod2CycleSupportEdges
        K hcore v f :=
    (mem_vertexLinkMod2CycleSupportEdges_iff
      K hcore v f e₀).2 he₀ne

  have supportEdgeAdj :
      ∀ e : VertexLinkMod2Edge K hcore v,
        e ∈ vertexLinkMod2CycleSupportEdges
            K hcore v f →
          G.Adj
            (vertexLinkMod2EdgeLoVertex K hcore v e)
            (vertexLinkMod2EdgeHiVertex K hcore v e) := by
    intro e he
    simp only [
      G,
      vertexLinkMod2CycleSupportGraph,
      SimpleGraph.fromRel_adj
    ]
    refine ⟨?_, Or.inl ?_⟩
    · intro hEq
      have hVal :=
        congrArg
          (fun x : VertexLinkMod2Vertex K v => x.1)
          hEq
      have hEnds : e.1.lo = e.1.hi := by
        simpa using hVal
      exact (Nat.ne_of_lt e.1.sorted) hEnds
    · exact ⟨e, he, rfl, rfl⟩

  let u :=
    vertexLinkMod2EdgeLoVertex K hcore v e₀
  let w :=
    vertexLinkMod2EdgeHiVertex K hcore v e₀

  have huw : u ≠ w := by
    intro hEq
    have hVal :=
      congrArg
        (fun x : VertexLinkMod2Vertex K v => x.1)
        hEq
    have hEnds : e₀.1.lo = e₀.1.hi := by
      simpa [u, w] using hVal
    exact (Nat.ne_of_lt e₀.1.sorted) hEnds

  have huwAdj : G.Adj u w := by
    simpa [u, w] using supportEdgeAdj e₀ he₀

  let C : G.ConnectedComponent :=
    G.connectedComponentMk u

  have huC : u ∈ C := by
    rfl

  have hwC : w ∈ C :=
    C.mem_supp_of_adj_mem_supp huC huwAdj

  let uC : C := ⟨u, huC⟩
  let wC : C := ⟨w, hwC⟩

  have huCwC : uC ≠ wC := by
    intro hEq
    apply huw
    have hVal := congrArg (fun z : C => z.1) hEq
    simpa [uC, wC] using hVal

  letI : Nontrivial C :=
    ⟨⟨uC, wC, huCwC⟩⟩

  letI : Fintype C :=
    Fintype.ofFinite C

  by_contra hnoCycle

  have hacyclic : G.IsAcyclic := by
    intro x c hc
    exact hnoCycle ⟨x, c, hc⟩

  have htree : C.toSimpleGraph.IsTree :=
    hacyclic.isTree_connectedComponent C

  rcases htree.exists_vert_degree_one_of_nontrivial with
    ⟨leaf, hleafDegree⟩

  rcases
      (SimpleGraph.degree_eq_one_iff_existsUnique_adj).1
        hleafDegree with
    ⟨nbr, hleafNbr, huniq⟩

  have hleafNbrG : G.Adj leaf.1 nbr.1 :=
    (C.toSimpleGraph_adj leaf.2 nbr.2).1 hleafNbr

  have hleafNbrData :
      leaf.1 ≠ nbr.1 ∧
        ((∃ e : VertexLinkMod2Edge K hcore v,
            e ∈ vertexLinkMod2CycleSupportEdges
                K hcore v f ∧
            leaf.1.1 = e.1.lo ∧
            nbr.1.1 = e.1.hi) ∨
         (∃ e : VertexLinkMod2Edge K hcore v,
            e ∈ vertexLinkMod2CycleSupportEdges
                K hcore v f ∧
            nbr.1.1 = e.1.lo ∧
            leaf.1.1 = e.1.hi)) := by
    simpa [G, vertexLinkMod2CycleSupportGraph] using
      hleafNbrG

  rcases hleafNbrData with ⟨_, hrel⟩

  have hcurrent :
      ∃ e : VertexLinkMod2Edge K hcore v,
        e ∈ vertexLinkMod2CycleSupportEdges
            K hcore v f ∧
        ((leaf.1.1 = e.1.lo ∧
            e.1.hi = nbr.1.1) ∨
         (leaf.1.1 = e.1.hi ∧
            e.1.lo = nbr.1.1)) := by
    rcases hrel with
      ⟨e, he, hleaf, hnbr⟩ |
      ⟨e, he, hnbr, hleaf⟩
    · exact
        ⟨e, he, Or.inl ⟨hleaf, hnbr.symm⟩⟩
    · exact
        ⟨e, he, Or.inr ⟨hleaf, hnbr.symm⟩⟩

  rcases hcurrent with ⟨e, he, hcurrentEnds⟩

  have hleafIncident :
      leaf.1.1 = e.1.lo ∨
      leaf.1.1 = e.1.hi := by
    rcases hcurrentEnds with hcur | hcur
    · exact Or.inl hcur.1
    · exact Or.inr hcur.1

  rcases
      vertexLinkMod2Cycle_exists_distinct_incident_support_edge
        K hcore v f hf leaf.1 e he hleafIncident with
    ⟨e', he', he'ne, hleafIncident'⟩

  have he'Adj := supportEdgeAdj e' he'

  have hother :
      (leaf.1.1 = e'.1.lo ∧
        e'.1.hi = nbr.1.1) ∨
      (leaf.1.1 = e'.1.hi ∧
        e'.1.lo = nbr.1.1) := by
    rcases hleafIncident' with hleafLo | hleafHi
    · left
      refine ⟨hleafLo, ?_⟩

      have hleafLoVertex :
          leaf.1 =
            vertexLinkMod2EdgeLoVertex
              K hcore v e' := by
        apply Subtype.ext
        simpa using hleafLo

      have hleafOtherAdj :
          G.Adj leaf.1
            (vertexLinkMod2EdgeHiVertex
              K hcore v e') := by
        rw [hleafLoVertex]
        exact he'Adj

      have hotherC :
          vertexLinkMod2EdgeHiVertex
              K hcore v e' ∈ C :=
        C.mem_supp_of_adj_mem_supp
          leaf.2 hleafOtherAdj

      let other : C :=
        ⟨vertexLinkMod2EdgeHiVertex
            K hcore v e', hotherC⟩

      have hleafOtherC :
          C.toSimpleGraph.Adj leaf other :=
        (C.toSimpleGraph_adj leaf.2 hotherC).2
          hleafOtherAdj

      have hotherEq : other = nbr :=
        huniq other hleafOtherC

      have hVal :=
        congrArg (fun z : C => z.1.1) hotherEq

      simpa [other] using hVal

    · right
      refine ⟨hleafHi, ?_⟩

      have hleafHiVertex :
          leaf.1 =
            vertexLinkMod2EdgeHiVertex
              K hcore v e' := by
        apply Subtype.ext
        simpa using hleafHi

      have hleafOtherAdj :
          G.Adj leaf.1
            (vertexLinkMod2EdgeLoVertex
              K hcore v e') := by
        rw [hleafHiVertex]
        exact he'Adj.symm

      have hotherC :
          vertexLinkMod2EdgeLoVertex
              K hcore v e' ∈ C :=
        C.mem_supp_of_adj_mem_supp
          leaf.2 hleafOtherAdj

      let other : C :=
        ⟨vertexLinkMod2EdgeLoVertex
            K hcore v e', hotherC⟩

      have hleafOtherC :
          C.toSimpleGraph.Adj leaf other :=
        (C.toSimpleGraph_adj leaf.2 hotherC).2
          hleafOtherAdj

      have hotherEq : other = nbr :=
        huniq other hleafOtherC

      have hVal :=
        congrArg (fun z : C => z.1.1) hotherEq

      simpa [other] using hVal

  rcases hcurrentEnds with hcur | hcur
  · rcases hother with hoth | hoth
    · apply he'ne
      apply Subtype.ext
      cases hE' : e'.1 with
      | mk lo' hi' hsorted' =>
        cases hE : e.1 with
        | mk lo hi hsorted =>
          simp_all
    · have hleaf_lt_nbr : leaf.1.1 < nbr.1.1 := by
        calc
          leaf.1.1 = e.1.lo := hcur.1
          _ < e.1.hi := e.1.sorted
          _ = nbr.1.1 := hcur.2
      have hnbr_lt_leaf : nbr.1.1 < leaf.1.1 := by
        calc
          nbr.1.1 = e'.1.lo := hoth.2.symm
          _ < e'.1.hi := e'.1.sorted
          _ = leaf.1.1 := hoth.1.symm
      omega
  · rcases hother with hoth | hoth
    · have hnbr_lt_leaf : nbr.1.1 < leaf.1.1 := by
        calc
          nbr.1.1 = e.1.lo := hcur.2.symm
          _ < e.1.hi := e.1.sorted
          _ = leaf.1.1 := hcur.1.symm
      have hleaf_lt_nbr : leaf.1.1 < nbr.1.1 := by
        calc
          leaf.1.1 = e'.1.lo := hoth.1
          _ < e'.1.hi := e'.1.sorted
          _ = nbr.1.1 := hoth.2
      omega
    · apply he'ne
      apply Subtype.ext
      cases hE' : e'.1 with
      | mk lo' hi' hsorted' =>
        cases hE : e.1 with
        | mk lo hi hsorted =>
          simp_all

end Poincare
