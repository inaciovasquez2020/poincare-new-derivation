import Poincare.GlobalMove32ReentryPolygonalLoop

namespace Poincare

/-- Simple connectivity supplies the full relative null-homotopy square for
the recurrence-driven polygonal loop.  In particular, this theorem applies
to the new ordered loop, not to `crossingPath.trans crossingPath.symm`. -/
theorem WitnessedReentryPolygonalLoopCertificate.exists_nullHomotopyData
    {K : Triangulation} (hSC : TriangulationRealizationSimplyConnected K)
    (c : WitnessedReentryPolygonalLoopCertificate K) :
    Nonempty (CarrierLoopNullHomotopyData K c.basepoint c.polygonalLoop) := by
  exact exists_carrierLoopNullHomotopyData hSC c.polygonalLoop

/-- The recurrent combinatorial certificate, its ordered polygonal loop, and
all four exact boundary equations of a relative null-homotopy can be chosen
simultaneously. -/
theorem ClosedTriangulationCore.exists_polygonalLoop_nullHomotopyData_of_witnessedReentry_recurrent_crossing
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hSC : TriangulationRealizationSimplyConnected K)
    (c : WitnessedReentryCrossingCertificate K)
    (hrealized : ∀ n, (c.sites n).RealizedIn K)
    (hthree : ∀ n, (c.sites n).SharedEdgeExactlyThree K)
    (hwitnessed : ∀ n,
      Move32SourceFaceWitnessedReentry K (c.sites n) (c.sites (n + 1))) :
    ∃ p : WitnessedReentryPolygonalLoopCertificate K,
      Nonempty (CarrierLoopNullHomotopyData K p.basepoint p.polygonalLoop) := by
  let p := (hcore.exists_polygonalLoopCertificate_of_witnessedReentry_recurrent_crossing
    c hrealized hthree hwitnessed).some
  exact ⟨p, p.exists_nullHomotopyData hSC⟩

end Poincare
