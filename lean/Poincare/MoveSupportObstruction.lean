import Poincare.FourSimplexBoundaryCombinatorialCertificate
import Poincare.Move23ClosedCorePreservation
import Poincare.Move32DegreeSupportBalance
import Poincare.CrossPolytopeBoundary

namespace Poincare

/-- A finite sequence consisting only of legal `2-3` and `3-2` bistellar
moves.  Closed-core evidence is recorded at each source because it is exactly
the hypothesis needed by the established `3-2` support theorem. -/
inductive LegalMove23Move32Sequence : Triangulation → Triangulation → Prop
  | refl (K : Triangulation) : LegalMove23Move32Sequence K K
  | move23 {K L : Triangulation}
      (hKL : LegalMove23Move32Sequence K L)
      (hcore : ClosedTriangulationCore L)
      (s : Move23Site) (hlegal : s.LegalIn L) :
      LegalMove23Move32Sequence K (s.replace L)
  | move32 {K L : Triangulation}
      (hKL : LegalMove23Move32Sequence K L)
      (hcore : ClosedTriangulationCore L)
      (s : Move32Site) (hlegal : s.LegalIn L) :
      LegalMove23Move32Sequence K (s.replace L)

/-- Finite legal `2-3`/`3-2` sequences preserve the represented vertex set. -/
theorem LegalMove23Move32Sequence.vertexSupport_mem_iff
    {K L : Triangulation} (hKL : LegalMove23Move32Sequence K L) (v : Nat) :
    v ∈ vertexSupport L ↔ v ∈ vertexSupport K := by
  induction hKL with
  | refl => rfl
  | move23 hKL _ s hlegal ih =>
      exact (s.replace_vertexSupport_mem_iff _ hlegal v).trans ih
  | move32 hKL hcore s hlegal ih =>
      exact (hcore.move32Site_replace_vertexSupport_mem_iff s hlegal v).trans ih

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

/-- The cross-polytope boundary cannot be normalized to zero supported defect
using only legal `2-3` and `3-2` moves.  Such moves preserve all eight of its
represented vertices, whereas a connected closed zero-defect triangulation
has exactly five represented vertices. -/
theorem crossPolytopeBoundary4_no_legalMove23Move32Sequence_to_PhiSupport_eq_zero :
    ¬ ∃ K : Triangulation,
      LegalMove23Move32Sequence crossPolytopeBoundary4 K ∧
      ClosedTriangulationCore K ∧
      TetrahedronVertexOverlapConnected K ∧
      PhiSupport K = 0 := by
  rintro ⟨K, hseq, hcore, hconn, hPhi⟩
  have hcardFive : (vertexSupport K).toFinset.card = 5 :=
    hcore.vertexSupport_toFinset_card_eq_five_of_PhiSupport_eq_zero hconn hPhi
  have hsupport :
      (vertexSupport K).toFinset = (vertexSupport crossPolytopeBoundary4).toFinset := by
    ext v
    simpa using hseq.vertexSupport_mem_iff v
  rw [hsupport, crossPolytopeBoundary4_vertexSupport] at hcardFive
  norm_num at hcardFive

end Poincare
