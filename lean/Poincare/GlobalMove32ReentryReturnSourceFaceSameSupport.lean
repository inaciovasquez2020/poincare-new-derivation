import Poincare.GlobalMove32ReentryReturnSourceFaceThirdVertex
import Mathlib.Tactic

namespace Poincare

/--
At a recurrent Move32 return, the third-vertex classification has only two
possibilities: either the anchor and return source faces have exactly the
same vertex support, or the two classified third vertices are distinct.

The first branch is precisely the `p = q` branch of
`exists_common_pair_and_third_sourceFace_vertices_of_return_target`.
No cycle-impossibility or termination conclusion is asserted here.
-/
theorem
    ClosedTriangulationCore.sourceFace_support_eq_or_distinct_third_vertices_of_return_target
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hretRealized : ret.RealizedIn K)
    (hretThree : ret.SharedEdgeExactlyThree K)
    {sigma : Tet}
    (hsigmaK : sigma ∈ K.tets)
    (hretD : ret.d ∈ sigma.verts)
    (hretE : ret.e ∈ sigma.verts)
    (hreturnEdge :
      (ret.d = anchor.d ∧ ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧ ret.e = anchor.d))
    (hanchorTarget :
      SameTetVertices sigma anchor.targetTet₀ ∨
      SameTetVertices sigma anchor.targetTet₁ ∨
      SameTetVertices sigma anchor.targetTet₂) :
    (∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] ↔
        z ∈ [ret.a, ret.b, ret.c]) ∨
    ∃ u v p q,
      u ≠ v ∧
      p ≠ u ∧
      p ≠ v ∧
      q ≠ u ∧
      q ≠ v ∧
      p ∈ [anchor.a, anchor.b, anchor.c] ∧
      q ∈ [ret.a, ret.b, ret.c] ∧
      (∀ z : Nat,
        z ∈ [anchor.a, anchor.b, anchor.c] ↔
        z = u ∨ z = v ∨ z = p) ∧
      (∀ z : Nat,
        z ∈ [ret.a, ret.b, ret.c] ↔
        z = u ∨ z = v ∨ z = q) ∧
      p ≠ q := by
  obtain
      ⟨u, v, p, q,
        huv,
        hpu,
        hpv,
        hqu,
        hqv,
        hpAnchor,
        hqRet,
        hanchorExact,
        hretExact⟩ :=
    hcore.exists_common_pair_and_third_sourceFace_vertices_of_return_target
      anchor
      ret
      hanchorRealized
      hretRealized
      hretThree
      hsigmaK
      hretD
      hretE
      hreturnEdge
      hanchorTarget

  by_cases hpq : p = q

  · left
    intro z
    constructor

    · intro hz
      have hz' :
          z = u ∨ z = v ∨ z = p :=
        (hanchorExact z).1 hz
      rw [hpq] at hz'
      exact
        (hretExact z).2 hz'

    · intro hz
      have hz' :
          z = u ∨ z = v ∨ z = q :=
        (hretExact z).1 hz
      rw [← hpq] at hz'
      exact
        (hanchorExact z).2 hz'

  · right
    exact
      ⟨u, v, p, q,
        huv,
        hpu,
        hpv,
        hqu,
        hqv,
        hpAnchor,
        hqRet,
        hanchorExact,
        hretExact,
        hpq⟩

end Poincare
