import Poincare.GlobalFanChordMove2332PrefixBalance
import Poincare.GlobalFanChordMove2332PrefixSourceFaceDegreeFourSplit

namespace Poincare

/-- Positive support defect may be stated on the original triangulation rather
than on the balanced legal `2-3,3-2` prefix output: prefix balance transfers it
exactly to the second source-face classification state. -/
theorem Move23Site.first_move32_prefix_exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction_of_original_PhiSupport_pos
    {K : Triangulation} (m : Move23Site) (s t : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlegal : m.LegalIn K)
    (hslegal : s.LegalIn (m.replace K))
    (hphi : 0 < PhiSupport K)
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
  have hphiPrefix : 0 < PhiSupport (s.replace (m.replace K)) := by
    rw [move2332Prefix_PhiSupport_eq hcore m hlegal s hslegal]
    exact hphi
  exact
    m.first_move32_prefix_exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction_of_PhiSupport_pos
      s t hcore hM hlegal hslegal hphiPrefix htrealized hobstruction

end Poincare
