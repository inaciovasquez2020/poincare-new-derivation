import Poincare.GlobalMove32ReentryReturnEscapeCrossEdgeIncidence
import Poincare.GlobalMove32IncidenceThreeWitnessedReentryNoOtherOutcome

namespace Poincare

/-- A witnessed return carrying a predecessor source vertex outside the anchor
carrier produces two distinct exact-three cross-edge seeds.  Under no strict
descent and no nonself high-edge escape, both seeds themselves carry witnessed
source-face reentries. -/
theorem
    ClosedTriangulationCore.exists_two_return_escape_witnessedReentry_seeds_of_noDescent_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
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
      q ∉ [anchor.a, anchor.b, anchor.c, anchor.d, anchor.e]) :
    ∃ sD sD' sE sE' : Move32Site,
      sD.d = q ∧
      sD.e = anchor.d ∧
      sD.RealizedIn K ∧
      sD.SharedEdgeExactlyThree K ∧
      Move32SourceFaceWitnessedReentry K sD sD' ∧
      sE.d = q ∧
      sE.e = anchor.e ∧
      sE.RealizedIn K ∧
      sE.SharedEdgeExactlyThree K ∧
      Move32SourceFaceWitnessedReentry K sE sE' ∧
      canonicalEdgeKey q anchor.d ≠ canonicalEdgeKey q anchor.e := by
  classical

  have hqD : q ≠ anchor.d := by
    intro h
    apply hqOutside
    simp [h]

  have hqE : q ≠ anchor.e := by
    intro h
    apply hqOutside
    simp [h]

  obtain ⟨hthreeD, hthreeE⟩ :=
    hcore.return_escape_crossEdges_incidence_three_of_noHigh
      anchor prev ret hanchorRealized hanchorObstruction hstep hreturn
      q hqPrev hqOutside hNoHigh

  have hthreeDDecide :
      (K.tets.filter
        (fun tau =>
          decide (q ∈ tau.verts ∧ anchor.d ∈ tau.verts))).length = 3 := by
    simpa using hthreeD

  have hthreeEDecide :
      (K.tets.filter
        (fun tau =>
          decide (q ∈ tau.verts ∧ anchor.e ∈ tau.verts))).length = 3 := by
    simpa using hthreeE

  obtain ⟨sD, sD', hsDd, hsDe, hsDRealized, hsDThree, hstepD⟩ :=
    hcore.exists_witnessedReentry_of_edgeIncidence_three_of_noDescent_noHigh
      hlinks hconn hNoFour hNoDescent hNoHigh
      q anchor.d hqD hthreeDDecide

  obtain ⟨sE, sE', hsEd, hsEe, hsERealized, hsEThree, hstepE⟩ :=
    hcore.exists_witnessedReentry_of_edgeIncidence_three_of_noDescent_noHigh
      hlinks hconn hNoFour hNoDescent hNoHigh
      q anchor.e hqE hthreeEDecide

  have hde : anchor.d ≠ anchor.e :=
    (hcore.move32_sharedEdge_supported anchor hanchorRealized).2.2

  have hkeys :
      canonicalEdgeKey q anchor.d ≠ canonicalEdgeKey q anchor.e := by
    intro hkey
    rcases
        (canonicalEdgeKey_eq_iff
          q anchor.d q anchor.e hqD hqE).1 hkey with
      hdirect | hreverse
    · exact hde hdirect.2
    · exact hqE hreverse.1

  exact
    ⟨sD, sD', sE, sE',
      hsDd, hsDe, hsDRealized, hsDThree, hstepD,
      hsEd, hsEe, hsERealized, hsEThree, hstepE,
      hkeys⟩

end Poincare
