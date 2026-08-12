import Poincare.VertexLinkMod2CycleParity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Poincare

open scoped BigOperators

/-- The exact finite set of represented link edges with nonzero coefficient. -/
def vertexLinkMod2CycleSupportEdges
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2) :
    Finset (VertexLinkMod2Edge K hcore v) :=
  Finset.univ.filter fun e => f e ≠ 0

@[simp]
theorem mem_vertexLinkMod2CycleSupportEdges_iff
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (e : VertexLinkMod2Edge K hcore v) :
    e ∈ vertexLinkMod2CycleSupportEdges K hcore v f ↔
      f e ≠ 0 := by
  simp [vertexLinkMod2CycleSupportEdges]

/--
Number of nonzero cycle-support edges incident to a represented link vertex.
-/
def vertexLinkMod2CycleSupportDegree
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (x : VertexLinkMod2Vertex K v) : Nat :=
  ((vertexLinkMod2CycleSupportEdges K hcore v f).filter
    fun e => x.1 = e.1.lo ∨ x.1 = e.1.hi).card

/-- A nonzero coefficient in `ZMod 2` is exactly one. -/
theorem zmod2_eq_one_of_ne_zero
    (a : ZMod 2)
    (ha : a ≠ 0) :
    a = 1 := by
  have hpos : 0 < a.val :=
    ZMod.val_pos.mpr ha
  have hlt : a.val < 2 :=
    ZMod.val_lt a
  have hval : a.val = 1 := by
    omega
  exact
    (ZMod.val_eq_one (n := 2) (by norm_num) a).mp hval

/--
The cast to `ZMod 2` of the finite support degree is exactly the coefficient
sum used by the represented boundary-one map.
-/
theorem vertexLinkMod2CycleSupportDegree_cast_eq_incident_sum
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (x : VertexLinkMod2Vertex K v) :
    ((vertexLinkMod2CycleSupportDegree K hcore v f x : Nat) : ZMod 2) =
      ∑ e : VertexLinkMod2Edge K hcore v,
        if x.1 = e.1.lo ∨ x.1 = e.1.hi
        then f e
        else 0 := by
  classical

  unfold vertexLinkMod2CycleSupportDegree
  unfold vertexLinkMod2CycleSupportEdges

  rw [Finset.card_eq_sum_ones]

  simp only [Nat.cast_sum, Nat.cast_one]

  rw [Finset.sum_filter]
  rw [Finset.sum_filter]

  apply Finset.sum_congr rfl
  intro e he

  by_cases hne : f e ≠ 0
  · have hone : f e = 1 :=
      zmod2_eq_one_of_ne_zero (f e) hne
    by_cases hinc :
        x.1 = e.1.lo ∨ x.1 = e.1.hi
    · simp [hne, hinc, hone]
    · simp [hne, hinc]
  · have hz : f e = 0 := by
      exact not_ne_iff.mp hne
    simp [hne, hz]

/--
Every represented vertex has even degree in the finite support of an exact
mod-2 one-cycle.
-/
theorem vertexLinkMod2CycleSupportDegree_even
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (hf :
      f ∈ LinearMap.ker
        (vertexLinkMod2BoundaryOne K hcore v))
    (x : VertexLinkMod2Vertex K v) :
    Even (vertexLinkMod2CycleSupportDegree K hcore v f x) := by
  apply ZMod.natCast_eq_zero_iff_even.mp

  rw [
    vertexLinkMod2CycleSupportDegree_cast_eq_incident_sum
      K hcore v f x
  ]

  exact
    vertexLinkMod2Cycle_incident_sum_eq_zero
      K hcore v f hf x

end Poincare
