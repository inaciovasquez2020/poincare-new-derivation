import Poincare.TriangulationTopologicalManifoldVertexLinkConnectedness

open Set

namespace Poincare

/-- An honest connected realization has a represented tetrahedron. -/
theorem exists_represented_tetrahedron_of_topologicalThreeManifold
    {K : Triangulation}
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K) :
    ∃ τ : Tet, τ ∈ K.tets := by
  rcases hM with ⟨_, _, _, _, hconnected⟩
  obtain ⟨x, _hx⟩ := hconnected.nonempty
  obtain ⟨F, _hF, ⟨τ, hτ, _hFτ⟩, _hxF⟩ :=
    (mem_triangulationTopologicalGeometricCarrier_iff K x.1).1 x.2
  exact ⟨τ, hτ⟩

/-- The endpoint tetrahedron required by normalization is supplied directly
by connected nonemptiness and the `ClosedTriangulationCore` validity field. -/
theorem ClosedTriangulationCore.exists_represented_nodup_tetrahedron
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K) :
    ∃ τ ∈ K.tets, τ.verts.Nodup := by
  obtain ⟨τ, hτ⟩ :=
    exists_represented_tetrahedron_of_topologicalThreeManifold hM
  exact ⟨τ, hτ, hcore.1 τ hτ⟩

end Poincare
