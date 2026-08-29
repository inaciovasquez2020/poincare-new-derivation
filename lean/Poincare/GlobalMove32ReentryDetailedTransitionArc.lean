import Poincare.GlobalMove32ReentryPolygonalLoop

open Set

namespace Poincare

/--
A witnessed-reentry transition arc with the middle source tetrahedron and the
exact halfway waypoint retained.  The halfway point of the canonical
three-segment trace is the represented vertex which becomes the first endpoint
of the next Move32 shared edge.

This is geometric bookkeeping needed to localize the least boundary escape.
It makes no termination, descent, or acyclicity claim.
-/
structure WitnessedReentryDetailedTransitionArc (K : Triangulation)
    (s t : Move32Site) (hs : s.RealizedIn K)
    extends WitnessedReentryTransitionArc K s t hs where
  sourceWitness : Tet
  sourceWitness_mem : sourceWitness ∈ K.tets
  source_a : s.a ∈ sourceWitness.verts
  source_b : s.b ∈ sourceWitness.verts
  source_c : s.c ∈ sourceWitness.verts
  nextD_mem_sourceWitness : t.d ∈ sourceWitness.verts
  nextD_not_sourceFace : t.d ∉ [s.a, s.b, s.c]
  half_nextD :
    (toWitnessedReentryTransitionArc.path
      (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval)).1 =
      triangulationTopologicalGeometricVertex t.d

/--
The canonical witnessed-reentry construction admits the detailed transition
arc above.  The proof uses the same three segments as
`witnessedReentry_transitionArc`; at parameter `1/2`, the outer concatenation
has finished the first two segments, and the inner concatenation is exactly at
the target represented vertex `x = t.d`.
-/
theorem witnessedReentry_detailedTransitionArc
    {K : Triangulation} (s t : Move32Site) (hs : s.RealizedIn K)
    (hstep : Move32SourceFaceWitnessedReentry K s t) :
    Nonempty (WitnessedReentryDetailedTransitionArc K s t hs) := by
  classical
  obtain ⟨target, htarget, htargetVerts⟩ := hs.1
  rcases hstep with
    ⟨tau, rho, x, y, sigma, htau, hrho, htrne,
      haTau, hbTau, hcTau, haRho, hbRho, hcRho,
      hxTau, hxabc, hyRho, hyabc, hxy, hsigma, hxSigma, hySigma,
      hnonself, htd, hte, ht, hthree, hobstruction⟩

  have haTarget : s.a ∈ target.verts :=
    (htargetVerts s.a).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  have hdTarget : s.d ∈ target.verts :=
    (htargetVerts s.d).2 (by simp [Move32Site.targetTet₀, Tet.verts])
  have heTarget : s.e ∈ target.verts :=
    (htargetVerts s.e).2 (by simp [Move32Site.targetTet₀, Tet.verts])

  have haSupport : s.a ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨target, htarget, haTarget⟩

  have hxSupport : x ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨tau, htau, hxTau⟩

  let pa := triangulationTopologicalCarrierVertex K s.a haSupport
  let px := triangulationTopologicalCarrierVertex K x hxSupport

  have hm0 : (move32SharedEdgeMidpoint s hs).1 ∈
      triangulationTopologicalTetBody target :=
    triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody hdTarget heTarget
  have hpa0 : pa.1 ∈ triangulationTopologicalTetBody target :=
    triangulationTopologicalGeometricVertex_mem_tetBody haTarget
  have hpa1 : pa.1 ∈ triangulationTopologicalTetBody tau :=
    triangulationTopologicalGeometricVertex_mem_tetBody haTau
  have hpx1 : px.1 ∈ triangulationTopologicalTetBody tau :=
    triangulationTopologicalGeometricVertex_mem_tetBody hxTau

  have hmt : (move32SharedEdgeMidpoint t ht).1 ∈
      triangulationTopologicalTetBody sigma := by
    apply triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody
    · simpa [htd] using hxSigma
    · simpa [hte] using hySigma

  have hpx2 : px.1 ∈ triangulationTopologicalTetBody sigma :=
    triangulationTopologicalGeometricVertex_mem_tetBody hxSigma

  let a0 := carrierSegmentInTet K target htarget _ _ hm0 hpa0
  let a1 := carrierSegmentInTet K tau htau _ _ hpa1 hpx1
  let a2 := carrierSegmentInTet K sigma hsigma _ _ hpx2 hmt

  let base : WitnessedReentryTransitionArc K s t hs := {
    targetRealized := ht
    path := (a0.trans a1).trans a2
    initialTarget := target
    initialTarget_mem := htarget
    initialTarget_same := htargetVerts
    initial_quarter_supported := by
      intro u hu
      have huHalf : (u : ℝ) ≤ 1 / 2 := by
        linarith
      have htwo : 2 * (u : ℝ) ≤ 1 / 2 := by
        linarith
      rw [Path.trans_apply]
      split_ifs with houter
      · rw [Path.trans_apply]
        split_ifs with hinner
        · exact carrierSegmentInTet_mem K target htarget _ _ hm0 hpa0 _
        · exact (hinner (by simpa using htwo)).elim
    supportingTets := [target, tau, sigma]
    supportingTets_mem := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    range_supported := by
      rw [Path.trans_range, Path.trans_range]
      rintro z ((⟨u, rfl⟩ | ⟨u, rfl⟩) | ⟨u, rfl⟩)
      · apply Set.mem_iUnion_of_mem target
        apply Set.mem_iUnion_of_mem (by simp)
        exact carrierSegmentInTet_mem K target htarget _ _ hm0 hpa0 u
      · apply Set.mem_iUnion_of_mem tau
        apply Set.mem_iUnion_of_mem (by simp)
        exact carrierSegmentInTet_mem K tau htau _ _ hpa1 hpx1 u
      · apply Set.mem_iUnion_of_mem sigma
        apply Set.mem_iUnion_of_mem (by simp)
        exact carrierSegmentInTet_mem K sigma hsigma _ _ hpx2 hmt u
  }

  refine ⟨{
    toWitnessedReentryTransitionArc := base
    sourceWitness := tau
    sourceWitness_mem := htau
    source_a := haTau
    source_b := hbTau
    source_c := hcTau
    nextD_mem_sourceWitness := by simpa [htd] using hxTau
    nextD_not_sourceFace := by simpa [htd] using hxabc
    half_nextD := ?_ }⟩

  change
    (((a0.trans a1).trans a2)
      (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval)).1 =
      triangulationTopologicalGeometricVertex t.d

  rw [Path.trans_apply]
  split_ifs with houter
  · rw [Path.trans_apply]
    split_ifs with hinner
    · norm_num at hinner
    · simp [a1, px, carrierSegmentInTet,
        triangulationTopologicalCarrierVertex, htd]
  · exact (houter (by norm_num)).elim

end Poincare
