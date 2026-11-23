/-!
G2 subdivided incidence-cone candidate.
STATUS: NOT_RUN. This file has NOT been compiled against the user's pinned
Lean 4.30.0-rc1 / Mathlib 05c4d64 toolchain.
Source basis: published work/first-nonzero-reentry-20261027,
lean/Poincare/PR199G2VerifiedConeComplex.lean (blob ef91ca5...).
No repository files have been modified.

This module isolates the precise combinatorial subdivided triangle that is
needed to index the two actual barycentric flags per graph edge. It deliberately
makes NO claim to prove the geometric homeomorphism yet.
-/

import Poincare.PR199G2VerifiedConeComplex

namespace Poincare.PR199G2

/-- Genuine incidences of graph edges with their endpoint fan vertices. -/
abbrev FanFlagIndex (K : Triangulation) (v x : Nat) :=
  Σ g : FanUnorderedGraphEdge K v x,
    {sigma :
      {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x} //
      sigma ∈ g.1}

/-- Three disjoint kinds of abstract vertices: the center, a tetrahedron
index, or an edge-face index. The `Sum` tag prevents conflating faces and
tetrahedra even if underlying labels happen to be equal. -/
abbrev FanSubdivVertex (K : Triangulation) (v x : Nat) :=
  Option (
    {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x} ⊕
    FanUnorderedGraphEdge K v x)

/-- Exactly one abstract triangle for each genuine graph edge-endpoint
incidence. Contrast the un-subdivided fanConeTriangle, indexed by a graph edge
alone. -/
noncomputable def fanSubdivFlagTriangle
    {K : Triangulation} {v x : Nat}
    (z : FanFlagIndex K v x) :
    Finset (FanSubdivVertex K v x) := by
  classical
  exact {none, some (Sum.inl z.2.1), some (Sum.inr z.1)}

/-- Each triangle has three distinct tagged vertices. -/
theorem fanSubdivFlagTriangle_card_three
    {K : Triangulation} {v x : Nat}
    (z : FanFlagIndex K v x) :
    (fanSubdivFlagTriangle z).card = 3 := by
  classical
  simp [fanSubdivFlagTriangle]

/-- Abstract intersection formula. The common center is always present;
a tetrahedron vertex is common precisely when the endpoints coincide; a face
vertex is common precisely when the graph edges coincide. This is the exact
combinatorial counterpart of closedCore_graphIndexed_completeIntersection. -/
theorem fanSubdivFlagTriangle_intersection
    {K : Triangulation} {v x : Nat}
    (z w : FanFlagIndex K v x) :
    fanSubdivFlagTriangle z ∩ fanSubdivFlagTriangle w =
      insert none
        ((if z.2.1 = w.2.1
          then ({some (Sum.inl z.2.1)} : Finset (FanSubdivVertex K v x))
          else ∅) ∪
         (if z.1 = w.1
          then ({some (Sum.inr z.1)} : Finset (FanSubdivVertex K v x))
          else ∅)) := by
  classical
  ext q
  cases q with
  | none =>
      simp [fanSubdivFlagTriangle]
  | some u =>
      cases u with
      | inl sigma =>
          by_cases hz : sigma = z.2.1
          · subst sigma
            by_cases hzw : z.2.1 = w.2.1
            · simp [fanSubdivFlagTriangle, hzw]
            · simp [fanSubdivFlagTriangle, hzw]
          · by_cases hzw : z.2.1 = w.2.1
            · simp [fanSubdivFlagTriangle, hz, hzw]
            · simp [fanSubdivFlagTriangle, hz, hzw]
      | inr g =>
          by_cases hz : g = z.1
          · subst g
            by_cases hzw : z.1 = w.1
            · simp [fanSubdivFlagTriangle, hzw]
            · simp [fanSubdivFlagTriangle, hzw]
          · by_cases hzw : z.1 = w.1
            · simp [fanSubdivFlagTriangle, hz, hzw]
            · simp [fanSubdivFlagTriangle, hz, hzw]

#print axioms fanSubdivFlagTriangle_card_three
#print axioms fanSubdivFlagTriangle_intersection

end Poincare.PR199G2