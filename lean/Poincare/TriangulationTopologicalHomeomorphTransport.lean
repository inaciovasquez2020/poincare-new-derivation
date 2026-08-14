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

end Poincare
