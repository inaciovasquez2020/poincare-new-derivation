import Poincare.GlobalFanChordMove2332PrefixSourceFaceOriginalPhi

namespace Poincare

/-- Any strict descent produced while classifying the balanced legal `2-3,3-2`
prefix state lifts back to a strict topology-preserving `PhiSupport` descent
from the original triangulation.  The high-edge and witnessed-reentry
alternatives remain based at the prefix output. -/
theorem Move23Site.first_move32_prefix_exists_original_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction_of_original_PhiSupport_pos
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
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
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
  rcases
      m.first_move32_prefix_exists_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction_of_original_PhiSupport_pos
        s t hcore hM hlegal hslegal hphi htrealized hobstruction with
    hdescent | hhigh | hreentry
  · obtain ⟨K', hcore', hlt, hhomeo⟩ := hdescent
    have hcore1 : ClosedTriangulationCore (m.replace K) :=
      hcore.move23Site_replace_closedCore m hlegal
    have hprefixHomeomorph :
        triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier (s.replace (m.replace K)) :=
      (hcore.move23GeometricCarrierHomeomorph m hlegal).trans
        (hcore1.move32GeometricCarrierHomeomorph s hslegal)
    have hbalance :=
      move2332Prefix_PhiSupport_eq hcore m hlegal s hslegal
    refine Or.inl ⟨K', hcore', ?_, ?_⟩
    · rw [← hbalance]
      exact hlt
    · obtain ⟨e⟩ := hhomeo
      exact ⟨hprefixHomeomorph.trans e⟩
  · exact Or.inr (Or.inl hhigh)
  · exact Or.inr (Or.inr hreentry)

end Poincare
