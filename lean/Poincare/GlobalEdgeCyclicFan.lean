import Poincare.TriangulationTopologicalManifoldVertexLinkStarConnectedness
import Poincare.GlobalEdgeIncidenceThreeStarAdjacency
import Poincare.Move32CombinatorialFoundation

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

/-- The shared edge of every realized incidence-three `Move32Site` is carried
by the exact three-triangle cyclic fan supplied by the honest manifold
structure.  This is the compiler-visible bridge from the Move32 recurrence
objects to the cyclic edge-fan API. -/
theorem ClosedTriangulationCore.exists_move32Site_sharedEdge_exact_coveringCycle_of_topologicalThreeManifold
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hthree : s.SharedEdgeExactlyThree K) :
    (vertexLinkStarTriangles K s.d s.e).length = 3 ∧
      ∃
        (sigma :
          {tau : LinkTriangle //
            tau ∈ vertexLinkStarTriangles K s.d s.e}),
        ∃
          (p : (vertexLinkStarGraph K s.d s.e).Walk sigma sigma),
          p.IsCycle ∧
          p.toSubgraph.verts =
            (Set.univ :
              Set
                {tau : LinkTriangle //
                  tau ∈ vertexLinkStarTriangles K s.d s.e}) := by
  have hdistinct := hcore.move32Site_distinct s hrealized
  have hde : s.d ≠ s.e := by
    simp [List.nodup_cons] at hdistinct
    aesop
  have hrep : VertexLinkVertexRepresented K s.d s.e :=
    (hcore.vertexLinkVertexRepresented_and_star_length_three_of_edgeIncidence_three
      s.d s.e hde hthree).1
  exact
    ⟨(hcore.vertexLinkVertexRepresented_and_star_length_three_of_edgeIncidence_three
        s.d s.e hde hthree).2,
      hcore.exists_vertexLinkStar_exact_coveringCycle_of_topologicalThreeManifold
        hM hrep⟩

end Poincare
