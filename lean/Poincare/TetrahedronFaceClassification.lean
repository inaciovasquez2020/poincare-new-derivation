import Poincare.Validity

namespace Poincare

/-- Three distinct represented vertices of a nondegenerate tetrahedron form
one of its four codimension-one faces.  The conclusion uses membership
equivalence, so it is insensitive to the order in which the three vertices
are presented. -/
theorem Tet.distinct_triple_face_cases
    (tau : Tet)
    (x y z : Nat)
    (hxyz : [x, y, z].Nodup)
    (hx : x ∈ tau.verts)
    (hy : y ∈ tau.verts)
    (hz : z ∈ tau.verts) :
    (∀ v, v = x ∨ v = y ∨ v = z ↔
      v = tau.v1 ∨ v = tau.v2 ∨ v = tau.v3) ∨
    (∀ v, v = x ∨ v = y ∨ v = z ↔
      v = tau.v0 ∨ v = tau.v2 ∨ v = tau.v3) ∨
    (∀ v, v = x ∨ v = y ∨ v = z ↔
      v = tau.v0 ∨ v = tau.v1 ∨ v = tau.v3) ∨
    (∀ v, v = x ∨ v = y ∨ v = z ↔
      v = tau.v0 ∨ v = tau.v1 ∨ v = tau.v2) := by
  simp [Tet.verts] at hxyz hx hy hz
  rcases hx with hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy | hy <;>
    rcases hz with hz | hz | hz | hz <;>
    subst_vars <;>
    simp_all [or_comm, or_left_comm, or_assoc]

end Poincare
