import Poincare.TriangulationTopologicalManifoldVertexLinkStarConnectedness

namespace Poincare

/-- A represented edge in an honest closed triangulated three-manifold has a
single finite cyclic fan whose subgraph contains every represented link
triangle in the edge star. -/
theorem ClosedTriangulationCore.exists_vertexLinkStar_exact_coveringCycle_of_topologicalThreeManifold
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x) :
    ∃
      (sigma :
        {tau : LinkTriangle //
          tau ∈ vertexLinkStarTriangles K v x}),
      ∃
        (p : (vertexLinkStarGraph K v x).Walk sigma sigma),
        p.IsCycle ∧
        p.toSubgraph.verts =
          (Set.univ :
            Set
              {tau : LinkTriangle //
                tau ∈ vertexLinkStarTriangles K v x}) := by
  exact
    exists_vertexLinkStar_coveringCycle
      K v x hrep
      (vertexLinkStarConnected_of_topologicalThreeManifold
        K hcore hM hrep)
      (hcore.vertexLinkStarDegreeTwo hrep)

/-- A represented edge in an honest closed triangulated three-manifold has a
single finite cyclic fan.  The vertices of the walk are precisely all link
triangles containing the transverse vertex, hence precisely the represented
tetrahedra around the edge after applying `linkTriangleAt?`. -/
theorem ClosedTriangulationCore.exists_vertexLinkStar_coveringCycle_of_topologicalThreeManifold
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v x : Nat}
    (hrep : VertexLinkVertexRepresented K v x) :
    ∃
      (sigma :
        {tau : LinkTriangle //
          tau ∈ vertexLinkStarTriangles K v x}),
      ∃
        (p : (vertexLinkStarGraph K v x).Walk sigma sigma),
        p.IsCycle ∧
        3 ≤ p.length ∧
        ∀ tau :
            {rho : LinkTriangle //
              rho ∈ vertexLinkStarTriangles K v x},
          tau ∈ p.support := by
  obtain ⟨sigma, p, hpcycle, hpcover⟩ :=
    hcore.exists_vertexLinkStar_exact_coveringCycle_of_topologicalThreeManifold
      hM hrep
  refine ⟨sigma, p, hpcycle, hpcycle.three_le_length, ?_⟩
  intro tau
  rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
  rw [hpcover]
  exact Set.mem_univ tau

end Poincare
