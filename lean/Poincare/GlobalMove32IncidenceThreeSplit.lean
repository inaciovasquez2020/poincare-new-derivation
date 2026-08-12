import Poincare.GlobalNoDegreeFourMove32Descent
import Mathlib.Tactic

namespace Poincare

/--
For a realized `3 → 2` candidate whose shared edge has exactly three
incident tetrahedra, legality has exactly one remaining possible failure:
the would-be source face `{a,b,c}` already occurs in a tetrahedron of `K`.
-/
theorem Move32Site.legal_or_sourceFace_obstruction_of_realized_sharedEdgeExactlyThree
    {K : Triangulation}
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hthree : s.SharedEdgeExactlyThree K) :
    s.LegalIn K ∨
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts := by

  by_cases hobs :
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts

  · exact Or.inr hobs

  · left

    refine ⟨hrealized, hthree, ?_⟩

    intro tau htau hface

    exact
      hobs
        ⟨tau,
          htau,
          hface⟩

/--
In the no-degree-four branch, a realized incidence-three `Move32Site`
therefore gives either an immediate topology-preserving strict
`PhiSupport` descent or an explicit source-face obstruction tetrahedron.
-/
theorem
    exists_closedCore_homeomorphic_PhiSupport_lt_or_sourceFace_obstruction_of_move32_incidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hthree : s.SharedEdgeExactlyThree K) :
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∃ tau ∈ K.tets,
      s.a ∈ tau.verts ∧
      s.b ∈ tau.verts ∧
      s.c ∈ tau.verts) := by

  rcases
    s.legal_or_sourceFace_obstruction_of_realized_sharedEdgeExactlyThree
      hrealized
      hthree
    with hlegal | hobs

  · left

    exact
      exists_closedCore_homeomorphic_PhiSupport_lt_of_move32_of_no_degree_four
        hcore
        hNoFour
        s
        hlegal

  · exact Or.inr hobs

/--
Fail-closed formulation used by the global coverage proof:
if a realized incidence-three candidate does not yield strict descent in
the no-degree-four branch, then the source-face obstruction actually exists.
-/
theorem
    move32_sourceFace_obstruction_of_no_descent_of_realized_incidence_three
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hthree : s.SharedEdgeExactlyThree K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K')) :
    ∃ tau ∈ K.tets,
      s.a ∈ tau.verts ∧
      s.b ∈ tau.verts ∧
      s.c ∈ tau.verts := by

  rcases
    exists_closedCore_homeomorphic_PhiSupport_lt_or_sourceFace_obstruction_of_move32_incidence_three
      hcore
      hNoFour
      s
      hrealized
      hthree
    with hdesc | hobs

  · exact (hNoDescent hdesc).elim

  · exact hobs

end Poincare
