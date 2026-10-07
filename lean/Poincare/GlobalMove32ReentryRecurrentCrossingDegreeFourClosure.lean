import Poincare.GlobalMove32PerpetualWitnessedReentryRecurrentCrossing
import Poincare.GlobalMove32BothSourcesNoDegreeFour

namespace Poincare

set_option maxHeartbeats 800000 in

/--
The finite recurrent crossing produced by perpetual witnessed reentry already
contains both source tetrahedra of its predecessor Move32 site.

At the crossing, tau contains the predecessor source face and the returned d,
while rho contains the same source face and the returned e.  Since d and e
are the two distinct shared-edge endpoints, tau and rho are representatives
of sourceTet₀ and sourceTet₁.  The existing five-tetrahedron theorem therefore
forces degree four, contradicting the no-degree-four branch.
-/
theorem
    ClosedTriangulationCore.not_perpetual_witnessedReentry_of_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ u ∈ vertexSupport K,
        VertexLinkConnected K u)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ u ∈ vertexSupport K,
        vertexDegree K u ≠ 4)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ x y sigma,
          x ≠ y ∧
          sigma ∈ K.tets ∧
          x ∈ sigma.verts ∧
          y ∈ sigma.verts ∧
          ¬ ((x = s.d ∧ y = s.e) ∨
             (x = s.e ∧ y = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (x ∈ gamma.verts ∧
                   y ∈ gamma.verts))).length)
    (start : Move32Site)
    (hstartRealized : start.RealizedIn K)
    (hstartThree : start.SharedEdgeExactlyThree K)
    (hstartObstruction :
      ∃ tau ∈ K.tets,
        start.a ∈ tau.verts ∧
        start.b ∈ tau.verts ∧
        start.c ∈ tau.verts) :
    False := by
  obtain ⟨sites, _hzero, hrealized, _hthree, _hobstruction, hwitnessed⟩ :=
    hcore.exists_perpetual_witnessedReentry_of_noDescent_noHigh
      hlinks hconn hNoFour hNoDescent hNoHigh
      start hstartRealized hstartThree hstartObstruction

  obtain ⟨i, k, tau, rho, _sigma, hconfig⟩ :=
    hcore.exists_finite_recurrent_return_crossing_configuration_of_perpetual_witnessedReentry
      sites hrealized _hthree hwitnessed

  rcases hconfig with
    ⟨_hgap, _hbound,
      htauK, hrhoK, _hsigmaK, hne,
      haTau, hbTau, hcTau,
      haRho, hbRho, hcRho,
      hdTau, heRho,
      _hdSigma, _heSigma,
      _heNotTau, _hdNotRho,
      _hsigmaTau, _hsigmaRho,
      hreturnEdge, _hsigmaTarget⟩

  have hs : Move32Site := sites k
  have hsRealized : hs.RealizedIn K := by
    simpa [hs] using hrealized k
  have haTau' : hs.a ∈ tau.verts := by simpa [hs] using haTau
  have hbTau' : hs.b ∈ tau.verts := by simpa [hs] using hbTau
  have hcTau' : hs.c ∈ tau.verts := by simpa [hs] using hcTau
  have hdTau' : hs.d ∈ tau.verts := by simpa [hs] using hdTau
  have haRho' : hs.a ∈ rho.verts := by simpa [hs] using haRho
  have hbRho' : hs.b ∈ rho.verts := by simpa [hs] using hbRho
  have hcRho' : hs.c ∈ rho.verts := by simpa [hs] using hcRho
  have heRho' : hs.e ∈ rho.verts := by simpa [hs] using heRho

  have habcd : [hs.a, hs.b, hs.c, hs.d].Nodup := by
    have h := hcore.move32Site_distinct hs (hrealized k)
    simp at h ⊢
    aesop

  have habce : [hs.a, hs.b, hs.c, hs.e].Nodup := by
    have h := hcore.move32Site_distinct hs (hrealized k)
    simp at h ⊢
    aesop

  have sameTetVertices_of_four_distinct_mem :
      ∀ (t : Tet) (a b c d : Nat),
        t.verts.Nodup →
        [a, b, c, d].Nodup →
        a ∈ t.verts →
        b ∈ t.verts →
        c ∈ t.verts →
        d ∈ t.verts →
        SameTetVertices t ⟨a, b, c, d⟩ := by
    intro t a b c d ht hlist ha hb hc hd
    classical
    let S : Finset Nat := t.verts.toFinset
    let T : Finset Nat := [a, b, c, d].toFinset
    have hsub : T ⊆ S := by
      intro z hz
      have hz' : z ∈ [a, b, c, d] := List.mem_toFinset.mp hz
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hz'
      apply List.mem_toFinset.mpr
      rcases hz' with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
      · exact hd
    have hScard : S.card = 4 := by
      dsimp [S]
      rw [List.toFinset_card_of_nodup ht]
      simp [Tet.verts]
    have hTcard : T.card = 4 := by
      dsimp [T]
      rw [List.toFinset_card_of_nodup hlist]
      simp
    have hEq : T = S :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    intro z
    constructor
    · intro hz
      have hzS : z ∈ S := List.mem_toFinset.mpr hz
      rw [← hEq] at hzS
      have hzT : z ∈ [a, b, c, d] := List.mem_toFinset.mp hzS
      simpa [Tet.verts] using hzT
    · intro hz
      have hzT : z ∈ [a, b, c, d] := by
        simpa [Tet.verts] using hz
      have hzFin : z ∈ T := List.mem_toFinset.mpr hzT
      rw [hEq] at hzFin
      exact List.mem_toFinset.mp hzFin

  have hsource0 :
      ∃ t ∈ K.tets,
        SameTetVertices t hs.sourceTet₀ := by
    refine ⟨tau, htauK, ?_⟩
    simpa [Move32Site.sourceTet₀] using
      sameTetVertices_of_four_distinct_mem
        tau hs.a hs.b hs.c hs.d
        (hcore.1 tau htauK)
        habcd
        haTau' hbTau' hcTau' hdTau'

  have hsource1 :
      ∃ t ∈ K.tets,
        SameTetVertices t hs.sourceTet₁ := by
    refine ⟨rho, hrhoK, ?_⟩
    simpa [Move32Site.sourceTet₁] using
      sameTetVertices_of_four_distinct_mem
        rho hs.a hs.b hs.c hs.e
        (hcore.1 rho hrhoK)
        habce
        haRho' hbRho' hcRho' heRho'

  exact
    hcore.not_both_move32_sources_represented_of_no_degree_four
      hlinks hconn hNoFour hs hsRealized hsource0 hsource1

end Poincare
