import Poincare.GlobalFiveTetDegreeFourConverse

namespace Poincare

/--
A global five-tetrahedron Move41 boundary cover is impossible in the
no-degree-four branch.

The global cover forces the center of the associated Move41 site to have
degree four.  The represented source tetrahedron places that center in the
ambient vertex support, contradicting the no-degree-four hypothesis.
-/
theorem
    ClosedTriangulationCore.not_global_fiveTet_cover_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move41Site)
    {tau0 tau1 tau2 tau3 target : Tet}
    (htau0K : tau0 ∈ K.tets)
    (htau0 :
      SameTetVertices tau0 s.sourceTet₀)
    (hglobal :
      ∀ rho ∈ K.tets,
        rho = tau0 ∨
        rho = tau1 ∨
        rho = tau2 ∨
        rho = tau3 ∨
        rho = target) :
    False := by
  have hdegree :
      vertexDegree K s.e = 4 :=
    hcore.vertexDegree_eq_four_of_global_fiveTet_cover
      s
      htau0K
      htau0
      hglobal

  have heSource :
      s.e ∈ s.sourceTet₀.verts := by
    simp [
      Move41Site.sourceTet₀,
      Tet.verts
    ]

  have heTau0 :
      s.e ∈ tau0.verts :=
    (htau0 s.e).2 heSource

  have heSupport :
      s.e ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    apply List.mem_flatMap.mpr
    exact ⟨tau0, htau0K, heTau0⟩

  exact
    (hNoFour s.e heSupport)
      hdegree

end Poincare
