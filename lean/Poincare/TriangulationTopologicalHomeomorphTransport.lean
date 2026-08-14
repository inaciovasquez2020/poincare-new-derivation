import Poincare.TriangulationTopologicalHonestManifold

namespace Poincare

/-- Simple connectivity of the canonical realization is invariant under a
homeomorphism of geometric carriers. -/
theorem triangulationRealizationSimplyConnected_of_homeomorph
    {K K' : Triangulation}
    (e : triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier K')
    (hSC : TriangulationRealizationSimplyConnected K) :
    TriangulationRealizationSimplyConnected K' := by
  exact e.toHomotopyEquiv.simplyConnectedSpace_iff.mp hSC

/-- Symmetric form of simple-connectivity invariance under a carrier
homeomorphism. -/
theorem triangulationRealizationSimplyConnected_homeomorph_iff
    {K K' : Triangulation}
    (e : triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier K') :
    TriangulationRealizationSimplyConnected K ↔
      TriangulationRealizationSimplyConnected K' := by
  constructor
  · exact triangulationRealizationSimplyConnected_of_homeomorph e
  · exact triangulationRealizationSimplyConnected_of_homeomorph e.symm

/-- The honest closed connected three-manifold predicate is invariant under
a homeomorphism of the canonical geometric carriers. -/
theorem
    triangulationRealizationIsClosedConnectedTopologicalThreeManifold_of_homeomorph
    {K K' : Triangulation}
    (e : triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier K')
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K) :
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K' := by
  rcases hM with ⟨hT2, hcharted, hmanifold, hcompact, hconnected⟩
  obtain ⟨x, _hx⟩ := hconnected.nonempty
  letI := hT2
  letI := hcharted
  letI := hmanifold
  letI : T2Space (triangulationTopologicalGeometricCarrier K') := e.t2Space
  letI : Nonempty (triangulationTopologicalGeometricCarrier K) :=
    ⟨x⟩
  letI : Nonempty (triangulationTopologicalGeometricCarrier K') :=
    ⟨e x⟩
  letI : ChartedSpace (triangulationTopologicalGeometricCarrier K)
      (triangulationTopologicalGeometricCarrier K') :=
    e.symm.isOpenEmbedding.singletonChartedSpace
  letI : ChartedSpace ThreeManifoldModel
      (triangulationTopologicalGeometricCarrier K') :=
    ChartedSpace.comp ThreeManifoldModel
      (triangulationTopologicalGeometricCarrier K)
      (triangulationTopologicalGeometricCarrier K')
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · simpa only [Set.image_univ, e.surjective.range_eq] using
      hcompact.image e.continuous
  · simpa only [Set.image_univ, e.surjective.range_eq] using
      hconnected.image e e.continuous.continuousOn

/-- Symmetric form of invariance of the honest manifold predicate. -/
theorem
    triangulationRealizationIsClosedConnectedTopologicalThreeManifold_homeomorph_iff
    {K K' : Triangulation}
    (e : triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier K') :
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K ↔
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K' := by
  constructor
  · exact
      triangulationRealizationIsClosedConnectedTopologicalThreeManifold_of_homeomorph e
  · exact
      triangulationRealizationIsClosedConnectedTopologicalThreeManifold_of_homeomorph e.symm

end Poincare
