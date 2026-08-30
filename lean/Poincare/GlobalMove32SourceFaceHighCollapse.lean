import Poincare.GlobalMove32SourceFaceSourceEdgeHigh
import Poincare.GlobalMove32IncidenceThreeSplit

namespace Poincare

/--
In the no-degree-four branch, a represented Move32 source-face obstruction
already supplies exactly the nonself high-incidence edge witness used by the
global fail-closed classification.  The witness is the source edge `a-b`
itself, carried by the represented source-face tetrahedron.
-/
theorem
    ClosedTriangulationCore.exists_nonself_sourceEdge_high_of_move32_sourceFace_obstruction_of_no_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hobstruction :
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts) :
    ∃ x y sigma,
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
               y ∈ gamma.verts))).length := by
  classical

  obtain ⟨theta, hthetaK, haTheta, hbTheta, _hcTheta⟩ := hobstruction

  have hfive :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hrealized

  have hab : s.a ≠ s.b := by
    have h := hfive
    simp at h
    aesop

  have had : s.a ≠ s.d := by
    have h := hfive
    simp at h
    aesop

  have hae : s.a ≠ s.e := by
    have h := hfive
    simp at h
    aesop

  have hnonself :
      ¬ ((s.a = s.d ∧ s.b = s.e) ∨
         (s.a = s.e ∧ s.b = s.d)) := by
    intro hself
    rcases hself with hdirect | hreverse
    · exact had hdirect.1
    · exact hae hreverse.1

  have hhigh :=
    hcore.move32_sourceEdge_ab_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
      hlinks hNoFour s hrealized
      ⟨theta, hthetaK, haTheta, hbTheta, _hcTheta⟩

  refine
    ⟨s.a, s.b, theta,
      hab,
      hthetaK,
      haTheta,
      hbTheta,
      hnonself,
      ?_⟩

  simpa using hhigh

/--
A realized exact-three `Move32Site` in the no-degree-four branch strictly
descends whenever the nonself high-incidence alternative is excluded for
that site.  The old source-face-obstruction branch is discharged directly by
the source-edge high-incidence theorem above, so no witnessed-reentry or
recurrence hypothesis is needed.
-/
theorem
    ClosedTriangulationCore.exists_closedCore_homeomorphic_PhiSupport_lt_of_move32_incidence_three_of_noHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hthree : s.SharedEdgeExactlyThree K)
    (hNoHigh :
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
    ∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K') := by
  rcases
      exists_closedCore_homeomorphic_PhiSupport_lt_or_sourceFace_obstruction_of_move32_incidence_three
        hcore hNoFour s hrealized hthree with
    hdescent | hobstruction

  · exact hdescent

  · exact
      (hNoHigh
        (hcore.exists_nonself_sourceEdge_high_of_move32_sourceFace_obstruction_of_no_degree_four
          hlinks hNoFour s hrealized hobstruction)).elim

end Poincare
