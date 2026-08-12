import Poincare.VertexLinkMod2Euler
import Mathlib.Tactic

namespace Poincare

open scoped BigOperators

/--
Coefficient-level form of the represented mod-2 boundary-one map:
at a represented link vertex `x`, `d₁ f` is the sum of the coefficients
of exactly those represented link edges incident to `x`.
-/
theorem vertexLinkMod2BoundaryOne_apply_eq_incident_sum
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (x : VertexLinkMod2Vertex K v) :
    vertexLinkMod2BoundaryOne K hcore v f x =
      ∑ e : VertexLinkMod2Edge K hcore v,
        if x.1 = e.1.lo ∨ x.1 = e.1.hi
        then f e
        else 0 := by
  classical
  simp [
    vertexLinkMod2BoundaryOne,
    vertexLinkMod2BoundaryOneMatrix,
    Matrix.mulVecLin_apply,
    Matrix.mulVec,
    dotProduct
  ]

/--
Every exact mod-2 one-cycle has zero endpoint-incidence coefficient sum at
each represented link vertex.

This is the finite combinatorial cycle condition extracted directly from
membership in `ker d₁`.
-/
theorem vertexLinkMod2Cycle_incident_sum_eq_zero
    (K : Triangulation)
    (hcore : ClosedTriangulationCore K)
    (v : Nat)
    (f : VertexLinkMod2Edge K hcore v → ZMod 2)
    (hf :
      f ∈ LinearMap.ker
        (vertexLinkMod2BoundaryOne K hcore v))
    (x : VertexLinkMod2Vertex K v) :
    (∑ e : VertexLinkMod2Edge K hcore v,
        if x.1 = e.1.lo ∨ x.1 = e.1.hi
        then f e
        else 0) = 0 := by
  rw [LinearMap.mem_ker] at hf
  have hx := congrFun hf x
  rw [
    vertexLinkMod2BoundaryOne_apply_eq_incident_sum
      K hcore v f x
  ] at hx
  simpa using hx

end Poincare
