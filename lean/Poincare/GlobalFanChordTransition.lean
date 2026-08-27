import Poincare.GlobalEdgeCyclicFanChordClassification
import Poincare.GlobalRepresentedEdgeIncidenceSplit
import Poincare.GlobalMove32SupportedEdgeState
import Poincare.GlobalMove32IncidenceThreeComposition
import Poincare.GlobalMove32WitnessedSourceFaceReentry
import Mathlib.Tactic

namespace Poincare

/-- The finite edge state and geometric escape data produced when the chord
of an adjacent pair in an ambient edge fan is already represented off the
old central edge.  The bridge tetrahedron retains the local carrier joining
the old central edge to one endpoint of the new chord.  In the high-incidence
branch `newFan` is an honest fan about the chord; no comparison of the two fan
sizes is asserted. -/
structure FanChordTransition (K : Triangulation) (v x : Nat) where
  z0 : Nat
  z1 : Nat
  endpoints_ne : z0 ≠ z1
  z0_supported : z0 ∈ vertexSupport K
  z1_supported : z1 ∈ vertexSupport K
  edgeState : SupportedEdgeState K
  edgeState_eq : edgeState =
    supportedEdgeStateOfDistinct K z0 z1 z0_supported z1_supported endpoints_ne
  bridge : Tet
  bridge_mem : bridge ∈ K.tets
  v_mem_bridge : v ∈ bridge.verts
  x_mem_bridge : x ∈ bridge.verts
  z0_mem_bridge : z0 ∈ bridge.verts
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
    have hz0bridge : z0 ∈ (F.tetAt sigma).verts :=
      (hleft z0).2 (by
        simp [Move23Site.leftTet, Tet.verts, ha, hb, hc, hd])
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
        bridge := F.tetAt sigma
        bridge_mem := F.tetAt_mem sigma
        v_mem_bridge := F.tetAt_contains_center sigma
        x_mem_bridge := F.tetAt_contains_edgeVertex sigma
        z0_mem_bridge := hz0bridge
        witness := tau, witness_mem := htau, z0_mem := hz0, z1_mem := hz1
        escapes_old_edge := hoff, incidence := Or.inl hinc }⟩
    · have hrep : VertexLinkVertexRepresented K z0 z1 :=
        hcore.vertexLinkVertexRepresented_of_edgeIncidence_pos z0 z1 hne hpos
      exact ⟨{
        z0 := z0, z1 := z1, endpoints_ne := hne
        z0_supported := hz0support, z1_supported := hz1support
        edgeState := supportedEdgeStateOfDistinct K z0 z1 hz0support hz1support hne
        edgeState_eq := rfl
        bridge := F.tetAt sigma
        bridge_mem := F.tetAt_mem sigma
        v_mem_bridge := F.tetAt_contains_center sigma
        x_mem_bridge := F.tetAt_contains_edgeVertex sigma
        z0_mem_bridge := hz0bridge
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

/-- Consume either certified incidence branch of a chord transition.

At incidence three this enters the existing `Move32` candidate/source-face
machinery.  At high incidence it selects an actual adjacent pair in the new
fan and applies the fan transition theorem again.  The source-face
obstruction is deliberately retained: eliminating it requires the separate
reentry dynamics, and is not a fan-chord transition by itself. -/
theorem ClosedTriangulationCore.FanChordTransition.continue
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    {v x : Nat} (T : FanChordTransition K v x) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∃ s : Move32Site,
      s.d = T.z0 ∧
      s.e = T.z1 ∧
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      ∃ tau ∈ K.tets,
        s.a ∈ tau.verts ∧
        s.b ∈ tau.verts ∧
        s.c ∈ tau.verts) ∨
    Nonempty (FanChordTransition K T.z0 T.z1) := by
  rcases T.incidence with hthree | hhigh
  · rcases
      hcore.exists_descent_or_realized_sourceFace_obstruction_of_edgeIncidence_three
        hNoFour T.z0 T.z1 T.endpoints_ne (by simpa using hthree) with
      hdescent | hobstruction
    · exact Or.inr (Or.inl hdescent)
    · exact Or.inr (Or.inr (Or.inl hobstruction))
  · rcases
      ClosedTriangulationCore.FanChordTransition.continue_high
        hcore hM T hhigh with
      hmove23 | hthree' | hnext
    · exact Or.inl hmove23
    · omega
    · exact Or.inr (Or.inr (Or.inr hnext))

/-- Consume a fan-chord transition through the witnessed source-face reentry
classification.  Unlike `continue`, this theorem does not leave a raw
incidence-three source-face obstruction: that obstruction is converted into
the existing witnessed reentry state (or one of its certified alternatives).

The last alternative is again a `FanChordTransition` about the output edge,
so the fan branch is genuinely composable. -/
theorem ClosedTriangulationCore.FanChordTransition.continue_witnessed
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    {v x : Nat} (T : FanChordTransition K v x) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∃ p q sigma,
      p ≠ q ∧
      sigma ∈ K.tets ∧
      p ∈ sigma.verts ∧
      q ∈ sigma.verts ∧
      4 ≤
        (K.tets.filter
          (fun gamma =>
            decide (p ∈ gamma.verts ∧ q ∈ gamma.verts))).length) ∨
    (∃ s s' : Move32Site,
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      Move32SourceFaceWitnessedReentry K s s') ∨
    Nonempty (FanChordTransition K T.z0 T.z1) := by
  rcases ClosedTriangulationCore.FanChordTransition.continue
      hcore hM hNoFour T with
    hmove23 | hdescent | hobstruction | hnext
  · exact Or.inl hmove23
  · exact Or.inr (Or.inl hdescent)
  · obtain ⟨s, _hsd, _hse, hrealized, hthree, hsource⟩ := hobstruction
    rcases
        hcore.exists_legal_move23_or_descent_or_nonself_complementEdge_high_or_witnessedReentry_of_move32_sourceFace_obstruction
          hlinks hconn hNoFour s hrealized hsource with
      hlegal | hdescent | hhigh | hreentry
    · exact Or.inl ⟨hlegal.choose, hlegal.choose_spec.2.2.2⟩
    · exact Or.inr (Or.inl hdescent)
    · obtain ⟨p, q, sigma, hpq, hsigma, hp, hq, _hnonself, hinc⟩ := hhigh
      exact Or.inr (Or.inr (Or.inl ⟨p, q, sigma, hpq, hsigma, hp, hq, hinc⟩))
    · obtain ⟨s', hstep⟩ := hreentry
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨s, s', hrealized, hthree, hstep⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hnext)))

end Poincare
