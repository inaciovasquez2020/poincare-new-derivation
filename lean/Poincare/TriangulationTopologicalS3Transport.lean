import Poincare.TriangulationTopologicalS3

namespace Poincare

/-- Genuine three-sphere recognition transports backward across a homeomorphism
of the canonical geometric carriers. -/
theorem triangulationRealizationHomeomorphicToThreeSphere_of_homeomorph
    {K K' : Triangulation}
    (e : triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier K')
    (hS3 : TriangulationRealizationHomeomorphicToThreeSphere K') :
    TriangulationRealizationHomeomorphicToThreeSphere K := by
  rcases hS3 with ⟨hK'⟩
  exact ⟨e.trans hK'⟩

end Poincare
