import Poincare.GlobalDegreeFourDescent
import Poincare.GlobalFanChordMove2332PrefixSourceFaceClassification

namespace Poincare

/-- On the legal `2-3,3-2` prefix output, positive support defect removes the
remaining degree-four side condition from the second source-face obstruction
classifier: a degree-four supported vertex already gives strict descent, while
the complementary branch supplies the required no-degree-four hypothesis. -/
theorem Move23Site.first_move32_prefix_exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction_of_PhiSupport_pos
    {K : Triangulation} (m : Move23Site) (s t : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlegal : m.LegalIn K)
    (hslegal : s.LegalIn (m.replace K))
    (hphi : 0 < PhiSupport (s.replace (m.replace K)))
    (htrealized : t.RealizedIn (s.replace (m.replace K)))
    (hobstruction :
      ∃ tau ∈ (s.replace (m.replace K)).tets,
        t.a ∈ tau.verts ∧
        t.b ∈ tau.verts ∧
        t.c ∈ tau.verts) :
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport (s.replace (m.replace K)) ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier (s.replace (m.replace K)) ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∃ x y sigma,
      x ≠ y ∧
      sigma ∈ (s.replace (m.replace K)).tets ∧
      x ∈ sigma.verts ∧
      y ∈ sigma.verts ∧
      ¬ ((x = t.d ∧ y = t.e) ∨
         (x = t.e ∧ y = t.d)) ∧
      4 ≤
        ((s.replace (m.replace K)).tets.filter
          (fun gamma =>
            decide
              (x ∈ gamma.verts ∧
               y ∈ gamma.verts))).length) ∨
    ∃ t' : Move32Site,
      Move32SourceFaceWitnessedReentry (s.replace (m.replace K)) t t' := by
  have hconnected :=
    m.first_move32_prefix_connectedLinkClosedCore
      s hcore hM hlegal hslegal
  have htop :=
    m.first_move32_prefix_topological_package
      s hcore hM hlegal hslegal
  rcases
      hconnected.1.exists_topology_preserving_PhiSupport_descent_or_no_degree_four
        hconnected.2 htop.2 hphi with
    hdescent | hNoFour
  · exact Or.inl hdescent
  · exact
      m.first_move32_prefix_exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
        s t hcore hM hlegal hslegal hNoFour htrealized hobstruction

end Poincare
