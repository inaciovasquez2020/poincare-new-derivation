import Poincare.GlobalEdgeCyclicFanChordClassification
import Poincare.GlobalRepresentedEdgeIncidenceSplit
import Poincare.GlobalMove32SupportedEdgeState
import Poincare.GlobalMove32IncidenceThreeComposition
import Poincare.GlobalMove32WitnessedSourceFaceReentry
import Poincare.GlobalMove32SourceFaceHighCollapse
import Poincare.Move41FourSourceConnectedLinkDegree
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
  sigma : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x}
  rho : {t : LinkTriangle // t ∈ vertexLinkStarTriangles K v x}
  adjacent : (vertexLinkStarGraph K v x).Adj sigma rho
  witness : Tet
  witness_mem : witness ∈ K.tets
  z0_mem : z0 ∈ witness.verts
  z1_mem : z1 ∈ witness.verts
  escapes_old_edge : v ∉ witness.verts ∨ x ∉ witness.verts
  incidence :
    (K.tets.filter (fun tau => z0 ∈ tau.verts ∧ z1 ∈ tau.verts)).length = 3 ∨
    (4 ≤ (K.tets.filter (fun tau => z0 ∈ tau.verts ∧ z1 ∈ tau.verts)).length ∧
      Nonempty (AmbientEdgeCyclicFan K z0 z1))
  transverse : Nat
  leftTet : Tet
  rightTet : Tet
  leftTet_mem : leftTet ∈ K.tets
  rightTet_mem : rightTet ∈ K.tets
  leftTet_match : SameTetVertices leftTet ⟨v, x, transverse, z0⟩
  rightTet_match : SameTetVertices rightTet ⟨v, x, transverse, z1⟩
  distinct : [v, x, transverse, z0, z1].Nodup

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
        sigma := sigma
        rho := rho
        adjacent := hadj
        witness := tau, witness_mem := htau, z0_mem := hz0, z1_mem := hz1
        escapes_old_edge := hoff, incidence := Or.inl hinc
        transverse := y
        leftTet := F.tetAt sigma
        rightTet := F.tetAt rho
        leftTet_mem := F.tetAt_mem sigma
        rightTet_mem := F.tetAt_mem rho
        leftTet_match := by
          simpa [Move23Site.leftTet, ha, hb, hc, hd] using hleft
        rightTet_match := by
          simpa [Move23Site.rightTet, ha, hb, hc, he] using hright
        distinct := by
          simpa [ha, hb, hc, hd, he] using m.distinct }⟩
    · have hrep : VertexLinkVertexRepresented K z0 z1 :=
        hcore.vertexLinkVertexRepresented_of_edgeIncidence_pos z0 z1 hne hpos
      exact ⟨{
        z0 := z0, z1 := z1, endpoints_ne := hne
        z0_supported := hz0support, z1_supported := hz1support
        edgeState := supportedEdgeStateOfDistinct K z0 z1 hz0support hz1support hne
        edgeState_eq := rfl
        sigma := sigma
        rho := rho
        adjacent := hadj
        witness := tau, witness_mem := htau, z0_mem := hz0, z1_mem := hz1
        escapes_old_edge := hoff
        incidence := Or.inr ⟨hinc,
          hcore.exists_ambientEdgeCyclicFan_of_topologicalThreeManifold hM hrep⟩
        transverse := y
        leftTet := F.tetAt sigma
        rightTet := F.tetAt rho
        leftTet_mem := F.tetAt_mem sigma
        rightTet_mem := F.tetAt_mem rho
        leftTet_match := by
          simpa [Move23Site.leftTet, ha, hb, hc, hd] using hleft
        rightTet_match := by
          simpa [Move23Site.rightTet, ha, hb, hc, he] using hright
        distinct := by
          simpa [ha, hb, hc, hd, he] using m.distinct }⟩


/-- Retained complement-carrier data for a fan-chord transition. -/
theorem FanChordTransition.complement_carrier_data
    {K : Triangulation} {v x : Nat}
    (T : FanChordTransition K v x) :
    T.leftTet ∈ K.tets ∧
    T.rightTet ∈ K.tets ∧
    SameTetVertices T.leftTet ⟨v, x, T.transverse, T.z0⟩ ∧
    SameTetVertices T.rightTet ⟨v, x, T.transverse, T.z1⟩ ∧
    [v, x, T.transverse, T.z0, T.z1].Nodup := by
  exact ⟨T.leftTet_mem, T.rightTet_mem, T.leftTet_match,
    T.rightTet_match, T.distinct⟩

/-- Same-transverse two-cycle gives the existing saturated four-source star. -/
theorem ClosedTriangulationCore.fanChord_twoCycle_same_transverse_degree_four
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    {v x z0 z1 y : Nat}
    (T0 : FanChordTransition K v x)
    (T1 : FanChordTransition K z0 z1)
    (hT0 : T0.z0 = z0 ∧ T0.z1 = z1 ∧ T0.transverse = y)
    (hT1 : T1.z0 = v ∧ T1.z1 = x ∧ T1.transverse = y) :
    vertexDegree K y = 4 := by
  rcases hT0 with ⟨hz0, hz1, hy⟩
  rcases hT1 with ⟨hreturn0, hreturn1, htrans⟩
  let s : Move41Site :=
    { a := v, b := x, c := z0, d := z1, e := y,
      distinct := by
        have hd := T0.distinct
        rw [hz0, hz1, hy] at hd
        simp [List.nodup_cons] at hd ⊢
        aesop }
  have hsource0 : SameTetVertices T0.leftTet s.sourceTet₀ := by
    intro w
    constructor
    · intro hw
      have hw' := (T0.leftTet_match w).1 hw
      simp [s, Move41Site.sourceTet₀, Tet.verts, hy, hz0] at hw' ⊢
      aesop
    · intro hw
      have hw' : w ∈ (⟨v, x, T0.transverse, T0.z0⟩ : Tet).verts := by
        simp [s, Move41Site.sourceTet₀, Tet.verts, hy, hz0] at hw ⊢
        aesop
      exact (T0.leftTet_match w).2 hw'
  have hsource1 : SameTetVertices T0.rightTet s.sourceTet₁ := by
    intro w
    constructor
    · intro hw
      have hw' := (T0.rightTet_match w).1 hw
      simp [s, Move41Site.sourceTet₁, Tet.verts, hy, hz1] at hw' ⊢
      aesop
    · intro hw
      have hw' : w ∈ (⟨v, x, T0.transverse, T0.z1⟩ : Tet).verts := by
        simp [s, Move41Site.sourceTet₁, Tet.verts, hy, hz1] at hw ⊢
        aesop
      exact (T0.rightTet_match w).2 hw'
  have hsource2 : SameTetVertices T1.leftTet s.sourceTet₂ := by
    simpa [s, Move41Site.sourceTet₂, hreturn0, htrans,
      or_assoc, or_left_comm, or_comm] using T1.leftTet_match
  have hsource3 : SameTetVertices T1.rightTet s.sourceTet₃ := by
    simpa [s, Move41Site.sourceTet₃, hreturn1, htrans,
      or_assoc, or_left_comm, or_comm] using T1.rightTet_match
  have hy : y ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨T0.leftTet, T0.leftTet_mem,
      (hsource0 y).2 (by simp [Move41Site.sourceTet₀, Tet.verts])⟩
  exact hcore.move41Site_center_vertexDegree_eq_four_of_represented_sources_connectedLink
    s T0.leftTet_mem hsource0 T0.rightTet_mem hsource1
    T1.leftTet_mem hsource2 T1.rightTet_mem hsource3 (hlinks y hy)

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

/-- Under the same fail-closed high-edge exclusion used by the global
Move32 analysis, the incidence-three branch of a fan-chord transition can no
longer end in a source-face obstruction.  It either produces an actual legal
`2-3` move, a strict topology-preserving `PhiSupport` descent, or another
high-incidence fan-chord transition. -/
theorem ClosedTriangulationCore.FanChordTransition.continue_noHigh
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    (hNoHigh :
      ∀ s : Move32Site,
        s.RealizedIn K →
        (∃ tau ∈ K.tets,
          s.a ∈ tau.verts ∧
          s.b ∈ tau.verts ∧
          s.c ∈ tau.verts) →
        ¬ ∃ p q sigma,
          p ≠ q ∧
          sigma ∈ K.tets ∧
          p ∈ sigma.verts ∧
          q ∈ sigma.verts ∧
          ¬ ((p = s.d ∧ q = s.e) ∨
             (p = s.e ∧ q = s.d)) ∧
          4 ≤
            (K.tets.filter
              (fun gamma =>
                decide
                  (p ∈ gamma.verts ∧
                   q ∈ gamma.verts))).length)
    {v x : Nat} (T : FanChordTransition K v x) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    Nonempty (FanChordTransition K T.z0 T.z1) := by
  rcases ClosedTriangulationCore.FanChordTransition.continue
      hcore hM hNoFour T with
    hmove23 | hdescent | hobstruction | hnext
  · exact Or.inl hmove23
  · exact Or.inr (Or.inl hdescent)
  · obtain ⟨s, _hsd, _hse, hrealized, _hthree, hsource⟩ := hobstruction
    exact
      (hNoHigh s hrealized hsource
        (hcore.exists_nonself_sourceEdge_high_of_move32_sourceFace_obstruction_of_no_degree_four
          hlinks hNoFour s hrealized hsource)).elim
  · exact Or.inr (Or.inr hnext)

end Poincare
