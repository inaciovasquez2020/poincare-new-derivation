import Poincare.FourSimplexBoundaryCombinatorialCertificate

namespace Poincare

/-- A connected closed triangulation with zero supported defect has exactly
five represented vertices. -/
theorem ClosedTriangulationCore.vertexSupport_toFinset_card_eq_five_of_PhiSupport_eq_zero
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hPhi : PhiSupport K = 0) :
    (vertexSupport K).toFinset.card = 5 := by
  obtain ⟨τ, hτK⟩ := hconn.1
  obtain ⟨ρ012, ρ013, ρ023, ρ123, e,
    _h012K, _h013K, _h023K, _h123K, _heτ, hdistinct,
    _hsupport, hsupportFinset, _htetsFinset,
    _hτFinset, _h012Finset, _h013Finset, _h023Finset, _h123Finset,
    _hglobal⟩ :=
      hcore.exists_fourSimplexBoundary_combinatorial_certificate
        hPhi hconn hτK (hcore.1 τ hτK)
  rw [hsupportFinset]
  simpa using List.toFinset_card_of_nodup hdistinct

end Poincare
