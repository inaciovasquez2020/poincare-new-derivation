import Poincare.Move32OneSourceEndpointDegree

namespace Poincare

theorem ClosedTriangulationCore.not_move32_sourceTet0_represented_of_no_degree_four_of_connectedLink
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hsource0 : ∃ tau ∈ K.tets, SameTetVertices tau s.sourceTet₀)
    (hconnected : VertexLinkConnected K s.d) : False := by
  obtain ⟨tau, htauK, hsame⟩ := hsource0
  have hdSupport : s.d ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htauK, (hsame s.d).2 (by
      simp [Move32Site.sourceTet₀, Tet.verts])⟩
  exact hNoFour s.d hdSupport
    (hcore.move32_sourceTet0_represented_vertexDegree_d_eq_four_of_connectedLink
      s hrealized ⟨tau, htauK, hsame⟩ hconnected)

theorem ClosedTriangulationCore.not_move32_sourceTet1_represented_of_no_degree_four_of_connectedLink
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hNoFour : ∀ v ∈ vertexSupport K, vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hsource1 : ∃ tau ∈ K.tets, SameTetVertices tau s.sourceTet₁)
    (hconnected : VertexLinkConnected K s.e) : False := by
  obtain ⟨tau, htauK, hsame⟩ := hsource1
  have heSupport : s.e ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htauK, (hsame s.e).2 (by
      simp [Move32Site.sourceTet₁, Tet.verts])⟩
  exact hNoFour s.e heSupport
    (hcore.move32_sourceTet1_represented_vertexDegree_e_eq_four_of_connectedLink
      s hrealized ⟨tau, htauK, hsame⟩ hconnected)

end Poincare
