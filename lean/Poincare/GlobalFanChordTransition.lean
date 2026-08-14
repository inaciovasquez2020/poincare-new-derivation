import Poincare.GlobalEdgeCyclicFanChordClassification
import Poincare.GlobalRepresentedEdgeIncidenceSplit
import Poincare.GlobalMove32SupportedEdgeState
import Mathlib.Tactic

namespace Poincare

/-- The finite edge state and geometric escape data produced when the chord
of an adjacent pair in an ambient edge fan is already represented off the
old central edge.  In the high-incidence branch `newFan` is an honest fan
about the chord; no comparison of the two fan sizes is asserted. -/
structure FanChordTransition (K : Triangulation) (v x : Nat) where
  z0 : Nat
  z1 : Nat
  endpoints_ne : z0 ≠ z1
  z0_supported : z0 ∈ vertexSupport K
  z1_supported : z1 ∈ vertexSupport K
  edgeState : SupportedEdgeState K
  edgeState_eq : edgeState =
    supportedEdgeStateOfDistinct K z0 z1 z0_supported z1_supported endpoints_ne
  witness : Tet
  witness_mem : witness ∈ K.tets
  z0_mem : z0 ∈ witness.verts
  z1_mem : z1 ∈ witness.verts
  escapes_old_edge : v ∉ witness.verts ∨ x ∉ witness.verts
  incidence :
    (K.tets.filter (fun tau => z0 ∈ tau.verts ∧ z1 ∈ tau.verts)).length = 3 ∨
    (4 ≤ (K.tets.filter (fun tau => z0 ∈ tau.verts ∧ z1 ∈ tau.verts)).length ∧
      Nonempty (AmbientEdgeCyclicFan K z0 z1))

/-- An obstructed adjacent `2-3` candidate either closes the old fan as an
incidence-three triangle, or gives a finite supported chord state with a
genuine off-old-edge carrier.  A chord of incidence at least four is equipped
with its own ambient cyclic fan. -/
theorem ClosedTriangulationCore.ambientEdgeCyclicFan_adjacent_transition
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v x : Nat} (F : AmbientEdgeCyclicFan K v x)
    {sigma rho} (hadj : (vertexLinkStarGraph K v x).Adj sigma rho) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (K.tets.filter (fun t => v ∈ t.verts ∧ x ∈ t.verts)).length = 3 ∨
    Nonempty (FanChordTransition K v x) := by
  classical
  obtain ⟨y, z0, z1, m, ha, hb, hc, hd, he, hleft, hright, hstatus⟩ :=
    hcore.ambientEdgeCyclicFan_adjacent_chord_classification F hadj
  rcases hstatus with hlegal | hthree | ⟨tau, htau, hz0, hz1, hoff⟩
  · exact Or.inl ⟨m, hlegal⟩
  · exact Or.inr (Or.inl hthree)
  · right; right
    have hfive : [v, x, y, z0, z1].Nodup := by
      simpa [ha, hb, hc, hd, he] using m.distinct
    have hne : z0 ≠ z1 := by
      simp [List.nodup_cons] at hfive
      tauto
    have hz0support : z0 ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      exact List.mem_flatMap.2 ⟨tau, htau, hz0⟩
    have hz1support : z1 ∈ vertexSupport K := by
      rw [mem_vertexSupport_iff]
      exact List.mem_flatMap.2 ⟨tau, htau, hz1⟩
    have hpos : 0 < (K.tets.filter
        (fun t => z0 ∈ t.verts ∧ z1 ∈ t.verts)).length := by
      apply List.length_pos_iff.2
      exact List.ne_nil_of_mem
        (List.mem_filter.2 ⟨htau, by simp [hz0, hz1]⟩)
    rcases hcore.edgeIncidence_eq_three_or_four_le_of_pos z0 z1 hne hpos with
      hinc | hinc
    · exact ⟨{
        z0 := z0, z1 := z1, endpoints_ne := hne
        z0_supported := hz0support, z1_supported := hz1support
        edgeState := supportedEdgeStateOfDistinct K z0 z1 hz0support hz1support hne
        edgeState_eq := rfl
        witness := tau, witness_mem := htau, z0_mem := hz0, z1_mem := hz1
        escapes_old_edge := hoff, incidence := Or.inl hinc }⟩
    · have hrep : VertexLinkVertexRepresented K z0 z1 :=
        hcore.vertexLinkVertexRepresented_of_edgeIncidence_pos z0 z1 hne hpos
      exact ⟨{
        z0 := z0, z1 := z1, endpoints_ne := hne
        z0_supported := hz0support, z1_supported := hz1support
        edgeState := supportedEdgeStateOfDistinct K z0 z1 hz0support hz1support hne
        edgeState_eq := rfl
        witness := tau, witness_mem := htau, z0_mem := hz0, z1_mem := hz1
        escapes_old_edge := hoff
        incidence := Or.inr ⟨hinc,
          hcore.exists_ambientEdgeCyclicFan_of_topologicalThreeManifold hM hrep⟩ }⟩

/-- The high-incidence output of a fan-chord transition is immediately
composable: choose an edge of its certified new fan and run the same local
transition theorem about the new central edge. -/
theorem ClosedTriangulationCore.FanChordTransition.continue_high
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    {v x : Nat} (T : FanChordTransition K v x)
    (hhigh :
      4 ≤ (K.tets.filter
        (fun tau => T.z0 ∈ tau.verts ∧ T.z1 ∈ tau.verts)).length ∧
      Nonempty (AmbientEdgeCyclicFan K T.z0 T.z1)) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (K.tets.filter
      (fun tau => T.z0 ∈ tau.verts ∧ T.z1 ∈ tau.verts)).length = 3 ∨
    Nonempty (FanChordTransition K T.z0 T.z1) := by
  obtain ⟨F⟩ := hhigh.2
  obtain ⟨sigma, rho, hadj⟩ := F.exists_adjacent
  exact hcore.ambientEdgeCyclicFan_adjacent_transition hM F hadj

end Poincare
