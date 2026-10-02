import Poincare.GlobalFanChordMove2332PrefixConnectedLinkClosedCore
import Poincare.GlobalMove32SourceFaceLegalMove23High

namespace Poincare

/-- After the legal `2-3,3-2` prefix, honest manifoldness of the original
triangulation supplies both connected vertex links and tetrahedron-overlap
connectedness needed by the second source-face obstruction classifier.  The
only remaining structural side condition here is exclusion of degree four on
the prefix output. -/
theorem Move23Site.first_move32_prefix_exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
    {K : Triangulation} (m : Move23Site) (s t : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlegal : m.LegalIn K)
    (hslegal : s.LegalIn (m.replace K))
    (hNoFour :
      ∀ v ∈ vertexSupport (s.replace (m.replace K)),
        vertexDegree (s.replace (m.replace K)) v ≠ 4)
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
  exact
    hconnected.1.exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
      hconnected.2 htop.2 hNoFour t htrealized hobstruction

end Poincare
