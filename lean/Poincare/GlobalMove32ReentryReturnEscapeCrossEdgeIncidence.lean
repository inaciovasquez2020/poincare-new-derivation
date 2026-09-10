import Poincare.GlobalMove32ReentryPredecessorCarrierEscape
import Poincare.GlobalRepresentedEdgeIncidenceSplit

namespace Poincare

/-- If a witnessed source-face reentry returns to an anchor shared edge and a
predecessor source-face vertex lies outside the anchor five-vertex carrier,
then exclusion of nonself high-edge escape forces both represented cross-edges
from that outside vertex to the anchor shared-edge endpoints to have exact
tetrahedron incidence three. -/
theorem
    ClosedTriangulationCore.return_escape_crossEdges_incidence_three_of_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (anchor prev ret : Move32Site)
    (hanchorRealized : anchor.RealizedIn K)
    (hanchorObstruction :
      ∃ tau ∈ K.tets,
        anchor.a ∈ tau.verts ∧
        anchor.b ∈ tau.verts ∧
        anchor.c ∈ tau.verts)
    (hstep : Move32SourceFaceWitnessedReentry K prev ret)
    (hreturn :
      (ret.d = anchor.d ∧ ret.e = anchor.e) ∨
      (ret.d = anchor.e ∧ ret.e = anchor.d))
    (q : Nat)
    (hqPrev : q ∈ [prev.a, prev.b, prev.c])
    (hqOutside :
      q ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e])
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
                   y ∈ gamma.verts))).length) :
    (K.tets.filter
        (fun tau => q ∈ tau.verts ∧ anchor.d ∈ tau.verts)).length = 3 ∧
    (K.tets.filter
        (fun tau => q ∈ tau.verts ∧ anchor.e ∈ tau.verts)).length = 3 := by
  classical

  have hqD : q ≠ anchor.d := by
    intro h
    apply hqOutside
    simp [h]

  have hqE : q ≠ anchor.e := by
    intro h
    apply hqOutside
    simp [h]

  have hstepKeep := hstep
  rcases hstepKeep with
    ⟨tau, rho, x, y, _sigma,
      htauK, hrhoK, _hne,
      haTau, hbTau, hcTau,
      haRho, hbRho, hcRho,
      hxTau, _hxABC,
      hyRho, _hyABC,
      _hxy,
      _hsigmaK, _hxSigma, _hySigma,
      _hnonself,
      hretD, hretE,
      _hretRealized, _hretThree, _hobstruction⟩

  have hqTau : q ∈ tau.verts := by
    have h := hqPrev
    simp only [List.mem_cons, List.mem_singleton] at h
    rcases h with h | h | h
    · simpa [h] using haTau
    · simpa [h] using hbTau
    · simpa [h] using hcTau

  have hqRho : q ∈ rho.verts := by
    have h := hqPrev
    simp only [List.mem_cons, List.mem_singleton] at h
    rcases h with h | h | h
    · simpa [h] using haRho
    · simpa [h] using hbRho
    · simpa [h] using hcRho

  have hrepresentedD :
      ∃ sigmaD ∈ K.tets,
        q ∈ sigmaD.verts ∧ anchor.d ∈ sigmaD.verts := by
    rcases hreturn with hdirect | hreverse
    · have hxD : x = anchor.d := hretD.symm.trans hdirect.1
      exact ⟨tau, htauK, hqTau, by simpa [hxD] using hxTau⟩
    · have hyD : y = anchor.d := hretE.symm.trans hreverse.2
      exact ⟨rho, hrhoK, hqRho, by simpa [hyD] using hyRho⟩

  have hrepresentedE :
      ∃ sigmaE ∈ K.tets,
        q ∈ sigmaE.verts ∧ anchor.e ∈ sigmaE.verts := by
    rcases hreturn with hdirect | hreverse
    · have hyE : y = anchor.e := hretE.symm.trans hdirect.2
      exact ⟨rho, hrhoK, hqRho, by simpa [hyE] using hyRho⟩
    · have hxE : x = anchor.e := hretD.symm.trans hreverse.1
      exact ⟨tau, htauK, hqTau, by simpa [hxE] using hxTau⟩

  have hnonselfD :
      ¬ ((q = anchor.d ∧ anchor.d = anchor.e) ∨
         (q = anchor.e ∧ anchor.d = anchor.d)) := by
    intro h
    rcases h with h | h
    · exact hqD h.1
    · exact hqE h.1

  have hnonselfE :
      ¬ ((q = anchor.d ∧ anchor.e = anchor.e) ∨
         (q = anchor.e ∧ anchor.e = anchor.d)) := by
    intro h
    rcases h with h | h
    · exact hqD h.1
    · exact hqE h.1

  have hincD :
      (K.tets.filter
        (fun gamma => q ∈ gamma.verts ∧ anchor.d ∈ gamma.verts)).length = 3 := by
    have hpos :
        0 <
          (K.tets.filter
            (fun gamma => q ∈ gamma.verts ∧ anchor.d ∈ gamma.verts)).length := by
      apply List.length_pos_iff.2
      rcases hrepresentedD with ⟨sigmaD, hsigmaDK, hqSigma, hdSigma⟩
      exact List.ne_nil_of_mem
        (List.mem_filter.2 ⟨hsigmaDK, by simp [hqSigma, hdSigma]⟩)

    rcases hcore.edgeIncidence_eq_three_or_four_le_of_pos
        q anchor.d hqD hpos with hthree | hhigh
    · exact hthree
    · exfalso
      rcases hrepresentedD with ⟨sigmaD, hsigmaDK, hqSigma, hdSigma⟩
      have hhighDecide :
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (q ∈ gamma.verts ∧ anchor.d ∈ gamma.verts))).length := by
        simpa using hhigh
      exact
        (hNoHigh anchor hanchorRealized hanchorObstruction)
          ⟨q, anchor.d, sigmaD, hqD, hsigmaDK, hqSigma, hdSigma,
            hnonselfD, hhighDecide⟩

  have hincE :
      (K.tets.filter
        (fun gamma => q ∈ gamma.verts ∧ anchor.e ∈ gamma.verts)).length = 3 := by
    have hpos :
        0 <
          (K.tets.filter
            (fun gamma => q ∈ gamma.verts ∧ anchor.e ∈ gamma.verts)).length := by
      apply List.length_pos_iff.2
      rcases hrepresentedE with ⟨sigmaE, hsigmaEK, hqSigma, heSigma⟩
      exact List.ne_nil_of_mem
        (List.mem_filter.2 ⟨hsigmaEK, by simp [hqSigma, heSigma]⟩)

    rcases hcore.edgeIncidence_eq_three_or_four_le_of_pos
        q anchor.e hqE hpos with hthree | hhigh
    · exact hthree
    · exfalso
      rcases hrepresentedE with ⟨sigmaE, hsigmaEK, hqSigma, heSigma⟩
      have hhighDecide :
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (q ∈ gamma.verts ∧ anchor.e ∈ gamma.verts))).length := by
        simpa using hhigh
      exact
        (hNoHigh anchor hanchorRealized hanchorObstruction)
          ⟨q, anchor.e, sigmaE, hqE, hsigmaEK, hqSigma, heSigma,
            hnonselfE, hhighDecide⟩

  exact ⟨hincD, hincE⟩

end Poincare
