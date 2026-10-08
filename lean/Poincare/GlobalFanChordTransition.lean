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
  leftTet_link : leftTet.linkTriangleAt? v = some sigma.1
  rightTet_link : rightTet.linkTriangleAt? v = some rho.1
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
        leftTet_link := F.tetAt_link sigma
        rightTet_link := F.tetAt_link rho
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
        leftTet_link := F.tetAt_link sigma
        rightTet_link := F.tetAt_link rho
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

/-- If two transitions retain the same local fan location but choose different transverse carriers, both transverse vertices lie in both retained link triangles. This isolates the residual two-common-vertex case without asserting uniqueness. -/
theorem FanChordTransition.same_location_different_transverse_common
    {K : Triangulation} {v x : Nat}
    (T0 T1 : FanChordTransition K v x)
    (hσ : T0.sigma.1 = T1.sigma.1)
    (hρ : T0.rho.1 = T1.rho.1)
    (_hy : T0.transverse ≠ T1.transverse) :
    T0.transverse ∈ T0.sigma.1.verts ∧
    T0.transverse ∈ T0.rho.1.verts ∧
    T1.transverse ∈ T0.sigma.1.verts ∧
    T1.transverse ∈ T0.rho.1.verts := by
  have hv0 : T0.transverse ≠ v := by
    intro h
    have hd := T0.distinct
    have hv : v ∈ [x, T0.transverse, T0.z0, T0.z1] := by
      simp [h]
    exact (List.nodup_cons.mp hd).1 hv
  have hv1 : T1.transverse ≠ v := by
    intro h
    have hd := T1.distinct
    exact (List.nodup_cons.mp hd).1 (by simp [h])
  have hs0 :
      T0.transverse ∈ T0.sigma.1.verts := by
    exact
      (T0.leftTet.mem_linkTriangleAt?_iff
        v T0.transverse T0.sigma.1 T0.leftTet_link hv0).2
        ((T0.leftTet_match T0.transverse).2
          (by simp [Tet.verts]))
  have hr0 :
      T0.transverse ∈ T0.rho.1.verts := by
    exact
      (T0.rightTet.mem_linkTriangleAt?_iff
        v T0.transverse T0.rho.1 T0.rightTet_link hv0).2
        ((T0.rightTet_match T0.transverse).2
          (by simp [Tet.verts]))
  have hs1 :
      T1.transverse ∈ T1.sigma.1.verts := by
    exact
      (T1.leftTet.mem_linkTriangleAt?_iff
        v T1.transverse T1.sigma.1 T1.leftTet_link hv1).2
        ((T1.leftTet_match T1.transverse).2
          (by simp [Tet.verts]))
  have hr1 :
      T1.transverse ∈ T1.rho.1.verts := by
    exact
      (T1.rightTet.mem_linkTriangleAt?_iff
        v T1.transverse T1.rho.1 T1.rightTet_link hv1).2
        ((T1.rightTet_match T1.transverse).2
          (by simp [Tet.verts]))
  rw [← hσ] at hs1
  rw [← hρ] at hr1
  exact ⟨hs0, hr0, hs1, hr1⟩

/-- Different transverse carriers cannot realize the same adjacent fan location.
The two carriers would be three distinct common vertices of both link triangles,
forcing equality of their vertex sets, contrary to the closed-core link
triangulation. -/
theorem FanChordTransition.same_location_different_transverse_impossible
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    {v x : Nat}
    (T0 T1 : FanChordTransition K v x)
    (hσ : T0.sigma.1 = T1.sigma.1)
    (hρ : T0.rho.1 = T1.rho.1)
    (hy : T0.transverse ≠ T1.transverse) :
    False := by
  have hcommon :=
    T0.same_location_different_transverse_common T1 hσ hρ hy
  have hσmem : T0.sigma.1 ∈ vertexLinkTriangles K v := by
    exact
      (mem_vertexLinkStarTriangles_iff K v x T0.sigma.1).1
        T0.sigma.2 |>.1
  have hρmem : T0.rho.1 ∈ vertexLinkTriangles K v := by
    exact
      (mem_vertexLinkStarTriangles_iff K v x T0.rho.1).1
        T0.rho.2 |>.1
  have hσnodup : T0.sigma.1.verts.Nodup :=
    vertexLinkTriangles_triangle_nodup K hcore v T0.sigma.1 hσmem
  have hρnodup : T0.rho.1.verts.Nodup :=
    vertexLinkTriangles_triangle_nodup K hcore v T0.rho.1 hρmem
  have hxσ : x ∈ T0.sigma.1.verts :=
    ((mem_vertexLinkStarTriangles_iff K v x T0.sigma.1).1
      T0.sigma.2).2
  have hxρ : x ∈ T0.rho.1.verts :=
    ((mem_vertexLinkStarTriangles_iff K v x T0.rho.1).1
      T0.rho.2).2
  have hxy0 : x ≠ T0.transverse := by
     have h := (List.nodup_cons.mp (List.nodup_cons.mp T0.distinct).2).1
     simp at h
     exact h.1
  have hxy1 : x ≠ T1.transverse := by
    intro h
    have hnotmem := (List.nodup_cons.mp (List.nodup_cons.mp T1.distinct).2).1
    exact hnotmem (by simp [h])
  have hyt : T0.transverse ≠ T1.transverse := hy
  have hexhaust :
      ∀ (σ : LinkTriangle) (a b c : Nat),
        σ.verts.Nodup →
        a ∈ σ.verts →
        b ∈ σ.verts →
        c ∈ σ.verts →
        a ≠ b → a ≠ c → b ≠ c →
        ∀ q, q ∈ σ.verts → q = a ∨ q = b ∨ q = c := by
    intro σ a b c hnodup ha hb hc hab hac hbc q hq
    rcases σ with ⟨s0, s1, s2⟩
    simp [LinkTriangle.verts] at hnodup ha hb hc hq ⊢
    aesop
  have hσexhaust :
      ∀ q, q ∈ T0.sigma.1.verts →
        q = x ∨ q = T0.transverse ∨ q = T1.transverse := by
    intro q hq
    exact
      hexhaust T0.sigma.1 x T0.transverse T1.transverse
        hσnodup hxσ hcommon.1 hcommon.2.2.1 hxy0
        hxy1 hyt q hq
  have hρexhaust :
      ∀ q, q ∈ T0.rho.1.verts →
        q = x ∨ q = T0.transverse ∨ q = T1.transverse := by
    intro q hq
    exact
      hexhaust T0.rho.1 x T0.transverse T1.transverse
        hρnodup hxρ hcommon.2.1 hcommon.2.2.2 hxy0
        hxy1 hyt q hq
  let S : Finset Nat := T0.sigma.1.verts.toFinset
  let R : Finset Nat := T0.rho.1.verts.toFinset
  have hSR : S ⊆ R := by
    intro q hq
    have hq' : q ∈ T0.sigma.1.verts := List.mem_toFinset.mp hq
    rcases hσexhaust q hq' with rfl | rfl | rfl
    · exact List.mem_toFinset.mpr hxρ
    · exact List.mem_toFinset.mpr hcommon.2.1
    · exact List.mem_toFinset.mpr hcommon.2.2.2
  have hScard : S.card = 3 := by
    simpa [S, LinkTriangle.verts] using
      List.toFinset_card_of_nodup hσnodup
  have hRcard : R.card = 3 := by
    simpa [R, LinkTriangle.verts] using
      List.toFinset_card_of_nodup hρnodup
  have hEq : S = R :=
    Finset.eq_of_subset_of_card_le hSR (by omega)
  have hvertices :
      ∀ q, q ∈ T0.sigma.1.verts ↔ q ∈ T0.rho.1.verts := by
    intro q
    have hq := Finset.ext_iff.mp hEq q
    simpa [S, R] using hq
  have hpair := vertexLinkTriangles_pairwise_vertexSet_ne K hcore v
  have hpair_mem :
      ∀ (l : List LinkTriangle), l.Pairwise
        (fun σ ρ =>
          ¬ ∀ y : Nat, y ∈ σ.verts ↔ y ∈ ρ.verts) →
        ∀ {a b : LinkTriangle},
          a ∈ l →
          b ∈ l →
          a ≠ b →
          ¬ ∀ y : Nat, y ∈ a.verts ↔ y ∈ b.verts := by
    intro l hpair'
    induction hpair' with
    | nil =>
        intro a b ha hb hne
        simp at ha
    | @cons c l hhead htail ih =>
        intro a b ha hb hne
        have hsymm : ∀ {d e : LinkTriangle},
            (¬ ∀ y : Nat, y ∈ d.verts ↔ y ∈ e.verts) →
            (¬ ∀ y : Nat, y ∈ e.verts ↔ y ∈ d.verts) := by
          intro d e h hs
          exact h (fun q => (hs q).symm)
        rcases List.mem_cons.mp ha with rfl | haTail
        · have hbTail : b ∈ l := by
            rcases List.mem_cons.mp hb with h | h
            · exact (hne h.symm).elim
            · exact h
          exact hhead b hbTail
        · rcases List.mem_cons.mp hb with rfl | hbTail
          · exact hsymm (hhead a haTail)
          · exact ih haTail hbTail hne
  have hσρ : T0.sigma.1 ≠ T0.rho.1 := by
    intro h
    apply T0.adjacent.ne
    exact Subtype.ext h
  exact (hpair_mem (vertexLinkTriangles K v) hpair hσmem hρmem hσρ) hvertices

/-- Distinct retained neighbors give distinct fan-chord transitions.
The transition records its retained right link triangle, so equality of
transitions forces equality of the retained neighbor. -/
theorem FanChordTransition.distinct_of_rho_ne
    {K : Triangulation} {v x : Nat}
    (T0 T1 : FanChordTransition K v x)
    (hρ : T0.rho.1 ≠ T1.rho.1) :
    T0 ≠ T1 := by
  intro hT
  apply hρ
  exact congrArg (fun T : FanChordTransition K v x => T.rho.1) hT

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
    intro w
    constructor
    · intro hw
      have hw' := (T1.leftTet_match w).1 hw
      simp [s, Move41Site.sourceTet₂, Tet.verts, hreturn0, htrans] at hw' ⊢
      aesop
    · intro hw
      have hw' : w ∈ (⟨z0, z1, T1.transverse, T1.z0⟩ : Tet).verts := by
        simp [s, Move41Site.sourceTet₂, Tet.verts, hreturn0, htrans] at hw ⊢
        aesop
      exact (T1.leftTet_match w).2 hw'
  have hsource3 : SameTetVertices T1.rightTet s.sourceTet₃ := by
    intro w
    constructor
    · intro hw
      have hw' := (T1.rightTet_match w).1 hw
      simp [s, Move41Site.sourceTet₃, Tet.verts, hreturn1, htrans] at hw' ⊢
      aesop
    · intro hw
      have hw' : w ∈ (⟨z0, z1, T1.transverse, T1.z1⟩ : Tet).verts := by
        simp [s, Move41Site.sourceTet₃, Tet.verts, hreturn1, htrans] at hw ⊢
        aesop
      exact (T1.rightTet_match w).2 hw'
  have hy : y ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    exact ⟨T0.leftTet, T0.leftTet_mem,
      (hsource0 y).2 (by simp [s, Move41Site.sourceTet₀, Tet.verts])⟩
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

/-- A two-step return with the same transverse carrier is incompatible with
the no-degree-four hypothesis. This is the bounded bridge from the recurrent
edge-state cycle to the existing four-source obstruction. -/
theorem ClosedTriangulationCore.fanChord_twoCycle_same_transverse_impossible_noFour
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    {v x z0 z1 y : Nat}
    (T0 : FanChordTransition K v x)
    (T1 : FanChordTransition K z0 z1)
    (hT0 : T0.z0 = z0 ∧ T0.z1 = z1 ∧ T0.transverse = y)
    (hT1 : T1.z0 = v ∧ T1.z1 = x ∧ T1.transverse = y) :
    False := by
  have hy : y ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    exact List.mem_flatMap.2 ⟨T0.leftTet, T0.leftTet_mem,
      (T0.leftTet_match y).2 (by
        simp [hT0.2.2, Tet.verts])⟩
  exact hNoFour y hy
    (hcore.fanChord_twoCycle_same_transverse_degree_four
      hlinks T0 T1 hT0 hT1)

end Poincare
