import Poincare.GeometricCarrierPermutation
import Poincare.PositionStellarClosedCoreTransport
import Poincare.HeadStellarNormalForm

namespace Poincare

/-- A certified Pachner move up to reordering of tetrahedron records.
This does not redefine or weaken `CertifiedPachnerStep`. -/
def PermutationCertifiedPachnerStep (K L : Triangulation) : Prop :=
  ∃ A B : Triangulation,
    K.tets.Perm A.tets ∧
    CertifiedPachnerStep A B ∧
    B.tets.Perm L.tets

/-- Every permutation-certified Pachner move induces a genuine homeomorphism
of the Pi-space geometric realizations. No geometric conclusion is an
assumption of `PermutationCertifiedPachnerStep`. -/
theorem PermutationCertifiedPachnerStep.homeomorphic
    {K L : Triangulation} (h : PermutationCertifiedPachnerStep K L) :
    Nonempty (triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier L) := by
  rcases h with ⟨A, B, hKA, hstep, hBL⟩
  obtain ⟨e⟩ := hstep.homeomorphic
  exact ⟨(triangulationTopologicalGeometricCarrier_homeomorph_of_perm hKA).trans
    (e.trans (triangulationTopologicalGeometricCarrier_homeomorph_of_perm hBL))⟩

/-- Literal arbitrary-position fresh 1→4 insertion is certified up to the
tetrahedron-order permutations required by the head-only inverse constructor.
The center's freshness and the source's closed-core validity are explicit. -/
theorem Move41Site.insertFreshAt_permutationCertifiedMove14
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hcore : ClosedTriangulationCore K)
    (hfresh : s.e ∉ vertexSupport K) :
    PermutationCertifiedPachnerStep K
      (s.insertFreshAt K before after hsource hfresh) := by
  let rest := before ++ after
  have hpermSource : K.tets.Perm (s.targetTet :: rest) := by
    rw [hsource]
    exact List.perm_middle
  have hheadCore : ClosedTriangulationCore
      ({tets := s.targetTet :: rest} : Triangulation) :=
    hcore.of_tets_perm hpermSource
  have hfreshRest : ∀ τ ∈ rest, s.e ∉ τ.verts := by
    intro τ hτ hcenter
    apply hfresh
    apply (mem_vertexSupport_iff K s.e).2
    change s.e ∈ K.tets.flatMap Tet.verts
    apply List.mem_flatMap.mpr
    refine ⟨τ, ?_, hcenter⟩
    rw [hsource]
    rcases List.mem_append.mp hτ with hb | ha
    · exact List.mem_append.mpr (Or.inl hb)
    · exact List.mem_append.mpr
        (Or.inr (List.mem_cons_of_mem _ ha))
  have hlegal := s.headStellar_legal rest hheadCore hfreshRest
  have hstep : CertifiedPachnerStep
      ({tets := s.targetTet :: rest} : Triangulation)
      (s.headStellar rest) := by
    have h := CertifiedPachnerStep.move14 hlegal.closedCore s hlegal
    rw [s.replace_headStellar_exact] at h
    exact h
  have hpermTarget :
      (s.headStellar rest).tets.Perm
        (s.insertFreshAt K before after hsource hfresh).tets := by
    change (s.sourceTets ++ (before ++ after)).Perm
      (before ++ s.sourceTets ++ after)
    simpa [List.append_assoc] using
      (List.perm_append_comm_assoc before s.sourceTets after).symm
  exact ⟨{tets := s.targetTet :: rest}, s.headStellar rest,
    hpermSource, hstep, hpermTarget⟩

/-- Topological certification of arbitrary-position fresh 1→4 insertion.
This is a proved consequence of the permutation-certified move witness. -/
theorem Move41Site.insertFreshAt_homeomorphic
    (s : Move41Site) (K : Triangulation)
    (before after : List Tet)
    (hsource : K.tets = before ++ s.targetTet :: after)
    (hcore : ClosedTriangulationCore K)
    (hfresh : s.e ∉ vertexSupport K) :
    Nonempty (triangulationTopologicalGeometricCarrier K ≃ₜ
      triangulationTopologicalGeometricCarrier
        (s.insertFreshAt K before after hsource hfresh)) :=
  (s.insertFreshAt_permutationCertifiedMove14 K before after
    hsource hcore hfresh).homeomorphic

end Poincare
