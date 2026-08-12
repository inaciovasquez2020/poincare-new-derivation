import Poincare.VertexLinkMod2CycleSupport
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

end Poincare
