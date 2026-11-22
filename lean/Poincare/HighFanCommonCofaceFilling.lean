import Poincare.GlobalMove32ReentryDyadicGridVertices
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

import Poincare.GlobalFanReentryModeLinkedSuccessor
import Poincare.CarrierPolygonalPath
import Poincare.GlobalDegreeFourDescent
import Poincare.TriangulationTopologicalManifoldConnectedLinkClosedCore
import Poincare.TriangulationTopologicalHonestConnectedness

namespace Poincare




/--
Geometric realization of source-edge ab reinjection.

The old fan midpoint is connected to the new source-edge midpoint
through z0 = s.d. The two constituent straight segments are supported
by the old fan's left tetrahedron and the realized Move32 targetTet₀.
-/
theorem FanChordTransition.exists_sourceAB_reinjection_twoTet_arc
    {K : Triangulation} {v x : Nat}
    (T : FanChordTransition K v x)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hsd : s.d = T.z0)
    (_hse : s.e = T.z1) :
    ∃ (p q : triangulationTopologicalGeometricCarrier K)
      (tau : Tet)
      (gamma : Path p q),
      p.1 =
        triangulationTopologicalGeometricEdgeMidpoint v x ∧
      q.1 =
        triangulationTopologicalGeometricEdgeMidpoint s.a s.b ∧
      tau ∈ K.tets ∧
      Set.range gamma ⊆
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody T.leftTet) ∪
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody tau) := by
  classical

  obtain ⟨tau, htau, hsame⟩ := hrealized.1

  have hv : v ∈ T.leftTet.verts := by
    apply (T.leftTet_match v).2
    simp [Tet.verts]

  have hx : x ∈ T.leftTet.verts := by
    apply (T.leftTet_match x).2
    simp [Tet.verts]

  have hz : T.z0 ∈ T.leftTet.verts := by
    apply (T.leftTet_match T.z0).2
    simp [Tet.verts]

  have ha : s.a ∈ tau.verts := by
    apply (hsame s.a).2
    simp [Move32Site.targetTet₀, Tet.verts]

  have hb : s.b ∈ tau.verts := by
    apply (hsame s.b).2
    simp [Move32Site.targetTet₀, Tet.verts]

  have hd : s.d ∈ tau.verts := by
    apply (hsame s.d).2
    simp [Move32Site.targetTet₀, Tet.verts]

  have hp :
      triangulationTopologicalGeometricEdgeMidpoint v x ∈
        triangulationTopologicalTetBody T.leftTet :=
    triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody hv hx

  have hmleft :
      triangulationTopologicalGeometricVertex T.z0 ∈
        triangulationTopologicalTetBody T.leftTet :=
    triangulationTopologicalGeometricVertex_mem_tetBody hz

  have hmtau :
      triangulationTopologicalGeometricVertex T.z0 ∈
        triangulationTopologicalTetBody tau := by
    rw [← hsd]
    exact triangulationTopologicalGeometricVertex_mem_tetBody hd

  have hq :
      triangulationTopologicalGeometricEdgeMidpoint s.a s.b ∈
        triangulationTopologicalTetBody tau :=
    triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody ha hb

  let p : triangulationTopologicalGeometricCarrier K :=
    ⟨triangulationTopologicalGeometricEdgeMidpoint v x,
      triangulationTopologicalTetBody_subset_carrier
        K T.leftTet_mem hp⟩

  let m : triangulationTopologicalGeometricCarrier K :=
    ⟨triangulationTopologicalGeometricVertex T.z0,
      triangulationTopologicalTetBody_subset_carrier
        K T.leftTet_mem hmleft⟩

  let q : triangulationTopologicalGeometricCarrier K :=
    ⟨triangulationTopologicalGeometricEdgeMidpoint s.a s.b,
      triangulationTopologicalTetBody_subset_carrier K htau hq⟩

  let alpha :=
    carrierSegmentInTet K T.leftTet T.leftTet_mem
      p m hp hmleft

  let beta :=
    carrierSegmentInTet K tau htau
      m q hmtau hq

  refine ⟨p, q, tau, alpha.trans beta, rfl, rfl, htau, ?_⟩
  apply carrierPath_trans_range_subset alpha beta
  · rintro z ⟨t, rfl⟩
    exact carrierSegmentInTet_mem
      K T.leftTet T.leftTet_mem p m hp hmleft t
  · rintro z ⟨t, rfl⟩
    exact carrierSegmentInTet_mem
      K tau htau m q hmtau hq t





/--
Geometric realization of source-edge ab reinjection.

The old fan midpoint is connected to the new source-edge midpoint
through z0 = s.d. The two constituent straight segments are supported
by the old fan's left tetrahedron and the realized Move32 targetTet₀.
-/
theorem FanChordTransition.exists_sourceAC_reinjection_twoTet_arc
    {K : Triangulation} {v x : Nat}
    (T : FanChordTransition K v x)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    (hsd : s.d = T.z0)
    (_hse : s.e = T.z1) :
    ∃ (p q : triangulationTopologicalGeometricCarrier K)
      (tau : Tet)
      (gamma : Path p q),
      p.1 =
        triangulationTopologicalGeometricEdgeMidpoint v x ∧
      q.1 =
        triangulationTopologicalGeometricEdgeMidpoint s.a s.c ∧
      tau ∈ K.tets ∧
      Set.range gamma ⊆
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody T.leftTet) ∪
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody tau) := by
  classical

  obtain ⟨tau, htau, hsame⟩ := hrealized.2.1

  have hv : v ∈ T.leftTet.verts := by
    apply (T.leftTet_match v).2
    simp [Tet.verts]

  have hx : x ∈ T.leftTet.verts := by
    apply (T.leftTet_match x).2
    simp [Tet.verts]

  have hz : T.z0 ∈ T.leftTet.verts := by
    apply (T.leftTet_match T.z0).2
    simp [Tet.verts]

  have ha : s.a ∈ tau.verts := by
    apply (hsame s.a).2
    simp [Move32Site.targetTet₁, Tet.verts]

  have hb : s.c ∈ tau.verts := by
    apply (hsame s.c).2
    simp [Move32Site.targetTet₁, Tet.verts]

  have hd : s.d ∈ tau.verts := by
    apply (hsame s.d).2
    simp [Move32Site.targetTet₁, Tet.verts]

  have hp :
      triangulationTopologicalGeometricEdgeMidpoint v x ∈
        triangulationTopologicalTetBody T.leftTet :=
    triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody hv hx

  have hmleft :
      triangulationTopologicalGeometricVertex T.z0 ∈
        triangulationTopologicalTetBody T.leftTet :=
    triangulationTopologicalGeometricVertex_mem_tetBody hz

  have hmtau :
      triangulationTopologicalGeometricVertex T.z0 ∈
        triangulationTopologicalTetBody tau := by
    rw [← hsd]
    exact triangulationTopologicalGeometricVertex_mem_tetBody hd

  have hq :
      triangulationTopologicalGeometricEdgeMidpoint s.a s.c ∈
        triangulationTopologicalTetBody tau :=
    triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody ha hb

  let p : triangulationTopologicalGeometricCarrier K :=
    ⟨triangulationTopologicalGeometricEdgeMidpoint v x,
      triangulationTopologicalTetBody_subset_carrier
        K T.leftTet_mem hp⟩

  let m : triangulationTopologicalGeometricCarrier K :=
    ⟨triangulationTopologicalGeometricVertex T.z0,
      triangulationTopologicalTetBody_subset_carrier
        K T.leftTet_mem hmleft⟩

  let q : triangulationTopologicalGeometricCarrier K :=
    ⟨triangulationTopologicalGeometricEdgeMidpoint s.a s.c,
      triangulationTopologicalTetBody_subset_carrier K htau hq⟩

  let alpha :=
    carrierSegmentInTet K T.leftTet T.leftTet_mem
      p m hp hmleft

  let beta :=
    carrierSegmentInTet K tau htau
      m q hmtau hq

  refine ⟨p, q, tau, alpha.trans beta, rfl, rfl, htau, ?_⟩
  apply carrierPath_trans_range_subset alpha beta
  · rintro z ⟨t, rfl⟩
    exact carrierSegmentInTet_mem
      K T.leftTet T.leftTet_mem p m hp hmleft t
  · rintro z ⟨t, rfl⟩
    exact carrierSegmentInTet_mem
      K tau htau m q hmtau hq t





/--
When an obstructed fan chord cannot yield a legal 2-3 move,
reinjection can be selected on one of the two explicit source
edges a-b or a-c. Both have already certified geometric arcs.

Unlike the coarse fan_reinject constructor, this theorem
preserves which geometric source edge was selected.
-/
theorem ClosedTriangulationCore.exists_sourceAB_or_AC_fanReinjection
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks : ∀ u ∈ vertexSupport K, VertexLinkConnected K u)
    (hNoFour : ∀ u ∈ vertexSupport K, vertexDegree K u ≠ 4)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (old : HighFanState K)
    (s : Move32Site)
    (hsd : s.d = old.transition.z0)
    (hse : s.e = old.transition.z1)
    (hrealized : s.RealizedIn K)
    (hobstruction :
      ∃ theta ∈ K.tets,
        s.a ∈ theta.verts ∧
        s.b ∈ theta.verts ∧
        s.c ∈ theta.verts) :
    ∃ next : HighFanState K,
      FanReentryModeStep K (.fan old) (.fan next) ∧
      ((next.v = s.a ∧ next.x = s.b) ∨
       (next.v = s.a ∧ next.x = s.c)) := by
  classical

  have hfive :
      [s.a, s.b, s.c, s.d, s.e].Nodup :=
    hcore.move32Site_distinct s hrealized

  have hab : s.a ≠ s.b := by
    have h := hfive
    simp at h
    aesop

  have hac : s.a ≠ s.c := by
    have h := hfive
    simp at h
    aesop

  have hbc : s.b ≠ s.c := by
    have h := hfive
    simp at h
    aesop

  have habNonself :
      ¬ ((s.a = s.d ∧ s.b = s.e) ∨
         (s.a = s.e ∧ s.b = s.d)) := by
    have h := hfive
    simp at h
    aesop

  have hacNonself :
      ¬ ((s.a = s.d ∧ s.c = s.e) ∨
         (s.a = s.e ∧ s.c = s.d)) := by
    have h := hfive
    simp at h
    aesop

  have hkey_ne :
      canonicalEdgeKey s.a s.b ≠
        canonicalEdgeKey s.a s.c := by
    intro hkey
    rcases
        (canonicalEdgeKey_eq_iff
          s.a s.b s.a s.c hab hac).1 hkey with
      hdirect | hreverse
    · exact hbc hdirect.2
    · exact hab hreverse.2.symm

  obtain ⟨theta, htheta, ha, hb, hc⟩ := hobstruction

  have hhigh :=
    hcore.move32_all_sourceEdges_incidence_four_le_of_sourceFace_obstruction_of_no_degree_four
      hlinks hNoFour s hrealized
      ⟨theta, htheta, ha, hb, hc⟩

  by_cases habOld :
      canonicalEdgeKey s.a s.b =
        canonicalEdgeKey old.v old.x

  · have hacAway :
        canonicalEdgeKey s.a s.c ≠
          canonicalEdgeKey old.v old.x := by
      intro h
      exact hkey_ne (habOld.trans h.symm)

    rcases
        hcore.exists_legal_move23_or_highFanState_on_edge_of_edgeIncidence_four_le
          hM hac htheta ha hc hhigh.2.1 with
      hmove | ⟨next, hv, hx⟩

    · exact (hNoMove23 hmove).elim

    · have haway :
          canonicalEdgeKey next.v next.x ≠
            canonicalEdgeKey old.v old.x := by
        rw [hv, hx]
        exact hacAway

      have hnonself :
          ¬ ((next.v = s.d ∧ next.x = s.e) ∨
             (next.v = s.e ∧ next.x = s.d)) := by
        rw [hv, hx]
        exact hacNonself

      exact
        ⟨next,
          FanReentryModeStep.fan_reinject
            old next s hsd hse hrealized
            ⟨theta, htheta, ha, hb, hc⟩
            haway hnonself,
          Or.inr ⟨hv, hx⟩⟩

  · rcases
        hcore.exists_legal_move23_or_highFanState_on_edge_of_edgeIncidence_four_le
          hM hab htheta ha hb hhigh.1 with
      hmove | ⟨next, hv, hx⟩

    · exact (hNoMove23 hmove).elim

    · have haway :
          canonicalEdgeKey next.v next.x ≠
            canonicalEdgeKey old.v old.x := by
        rw [hv, hx]
        exact habOld

      have hnonself :
          ¬ ((next.v = s.d ∧ next.x = s.e) ∨
             (next.v = s.e ∧ next.x = s.d)) := by
        rw [hv, hx]
        exact habNonself

      exact
        ⟨next,
          FanReentryModeStep.fan_reinject
            old next s hsd hse hrealized
            ⟨theta, htheta, ha, hb, hc⟩
            haway hnonself,
          Or.inl ⟨hv, hx⟩⟩



/--
An obstructed fan chord admits a witness-preserving fan reinjection
and a continuous carrier arc supported by the union of two
represented tetrahedra.

This is an existential successor theorem. It does not assert that
every inhabitant of the coarse FanReentryModeStep relation has
this geometric support.
-/
theorem ClosedTriangulationCore.exists_geometric_fanReinjection
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks : ∀ u ∈ vertexSupport K, VertexLinkConnected K u)
    (hNoFour : ∀ u ∈ vertexSupport K, vertexDegree K u ≠ 4)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (old : HighFanState K)
    (s : Move32Site)
    (hsd : s.d = old.transition.z0)
    (hse : s.e = old.transition.z1)
    (hrealized : s.RealizedIn K)
    (hobstruction :
      ∃ theta ∈ K.tets,
        s.a ∈ theta.verts ∧
        s.b ∈ theta.verts ∧
        s.c ∈ theta.verts) :
    ∃ (next : HighFanState K)
      (p q : triangulationTopologicalGeometricCarrier K)
      (tau : Tet)
      (gamma : Path p q),
      FanReentryModeStep K (.fan old) (.fan next) ∧
      p.1 =
        triangulationTopologicalGeometricEdgeMidpoint old.v old.x ∧
      q.1 =
        triangulationTopologicalGeometricEdgeMidpoint next.v next.x ∧
      tau ∈ K.tets ∧
      Set.range gamma ⊆
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody old.transition.leftTet) ∪
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody tau) := by
  classical

  obtain ⟨next, hstep, hchoice⟩ :=
    hcore.exists_sourceAB_or_AC_fanReinjection
      hM hlinks hNoFour hNoMove23
      old s hsd hse hrealized hobstruction

  rcases hchoice with ⟨hv, hx⟩ | ⟨hv, hx⟩

  · obtain ⟨p, q, tau, gamma,
        hp, hq, htau, hrange⟩ :=
      old.transition.exists_sourceAB_reinjection_twoTet_arc
        s hrealized hsd hse

    refine ⟨next, p, q, tau, gamma,
      hstep, hp, ?_, htau, hrange⟩

    rw [hv, hx]
    exact hq

  · obtain ⟨p, q, tau, gamma,
        hp, hq, htau, hrange⟩ :=
      old.transition.exists_sourceAC_reinjection_twoTet_arc
        s hrealized hsd hse

    refine ⟨next, p, q, tau, gamma,
      hstep, hp, ?_, htau, hrange⟩

    rw [hv, hx]
    exact hq




/--
A recorded fan-chord transition has a continuous geometric
realization from the old edge midpoint to the chord midpoint.
The path runs through vertex z0 and is supported by at most
two represented tetrahedra.
-/
theorem FanChordTransition.exists_twoTet_continuousArc
    {K : Triangulation} {v x : Nat}
    (T : FanChordTransition K v x) :
    ∃ (p q : triangulationTopologicalGeometricCarrier K)
      (gamma : Path p q),
      p.1 =
        triangulationTopologicalGeometricEdgeMidpoint v x ∧
      q.1 =
        triangulationTopologicalGeometricEdgeMidpoint T.z0 T.z1 ∧
      Set.range gamma ⊆
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody T.leftTet) ∪
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody T.witness) := by
  classical

  have hv :
      v ∈ T.leftTet.verts := by
    apply (T.leftTet_match v).2
    simp [Tet.verts]

  have hx :
      x ∈ T.leftTet.verts := by
    apply (T.leftTet_match x).2
    simp [Tet.verts]

  have hzleft :
      T.z0 ∈ T.leftTet.verts := by
    apply (T.leftTet_match T.z0).2
    simp [Tet.verts]

  have hp :
      triangulationTopologicalGeometricEdgeMidpoint v x ∈
        triangulationTopologicalTetBody T.leftTet :=
    triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody
      hv hx

  have hm :
      triangulationTopologicalGeometricVertex T.z0 ∈
        triangulationTopologicalTetBody T.leftTet :=
    triangulationTopologicalGeometricVertex_mem_tetBody hzleft

  have hmw :
      triangulationTopologicalGeometricVertex T.z0 ∈
        triangulationTopologicalTetBody T.witness :=
    triangulationTopologicalGeometricVertex_mem_tetBody
      T.z0_mem

  have hq :
      triangulationTopologicalGeometricEdgeMidpoint
        T.z0 T.z1 ∈
        triangulationTopologicalTetBody T.witness :=
    triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody
      T.z0_mem T.z1_mem

  let p : triangulationTopologicalGeometricCarrier K :=
    ⟨triangulationTopologicalGeometricEdgeMidpoint v x,
      triangulationTopologicalTetBody_subset_carrier
        K T.leftTet_mem hp⟩

  let m : triangulationTopologicalGeometricCarrier K :=
    ⟨triangulationTopologicalGeometricVertex T.z0,
      triangulationTopologicalTetBody_subset_carrier
        K T.leftTet_mem hm⟩

  let q : triangulationTopologicalGeometricCarrier K :=
    ⟨triangulationTopologicalGeometricEdgeMidpoint
        T.z0 T.z1,
      triangulationTopologicalTetBody_subset_carrier
        K T.witness_mem hq⟩

  let alpha :=
    carrierSegmentInTet K T.leftTet T.leftTet_mem
      p m hp hm

  let beta :=
    carrierSegmentInTet K T.witness T.witness_mem
      m q hmw hq

  refine ⟨p, q, alpha.trans beta, rfl, rfl, ?_⟩

  apply carrierPath_trans_range_subset alpha beta

  · rintro z ⟨t, rfl⟩
    exact carrierSegmentInTet_mem
      K T.leftTet T.leftTet_mem p m hp hm t

  · rintro z ⟨t, rfl⟩
    exact carrierSegmentInTet_mem
      K T.witness T.witness_mem m q hmw hq t



/--
Fail-closed high-fan dynamics has a geometrically supported
successor: ordinary chord continuation or source-edge reinjection.

The existential witness retains the supporting tetrahedron and
the continuous path, unlike the coarse transition relation.
-/
theorem ClosedTriangulationCore.exists_geometric_highFan_successor
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks : ∀ u ∈ vertexSupport K, VertexLinkConnected K u)
    (hNoFour : ∀ u ∈ vertexSupport K, vertexDegree K u ≠ 4)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (old : HighFanState K) :
    ∃ (next : HighFanState K)
      (p q : triangulationTopologicalGeometricCarrier K)
      (tau : Tet)
      (gamma : Path p q),
      FanReentryModeStep K (.fan old) (.fan next) ∧
      p.1 =
        triangulationTopologicalGeometricEdgeMidpoint old.v old.x ∧
      q.1 =
        triangulationTopologicalGeometricEdgeMidpoint next.v next.x ∧
      tau ∈ K.tets ∧
      Set.range gamma ⊆
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody old.transition.leftTet) ∪
        (Subtype.val ⁻¹'
          triangulationTopologicalTetBody tau) := by
  classical

  rcases
      ClosedTriangulationCore.FanChordTransition.continue
        hcore hM hNoFour old.transition with
    hmove | hdescent | hobstruction | hnext

  · exact (hNoMove23 hmove).elim

  · exact (hNoDescent hdescent).elim

  · obtain ⟨s, hsd, hse, hrealized, _hthree, hsource⟩ :=
      hobstruction

    obtain ⟨next, p, q, tau, gamma,
        hstep, hp, hq, htau, hrange⟩ :=
      hcore.exists_geometric_fanReinjection
        hM hlinks hNoFour hNoMove23
        old s hsd hse hrealized hsource

    exact ⟨next, p, q, tau, gamma,
      hstep, hp, hq, htau, hrange⟩

  · obtain ⟨T'⟩ := hnext

    let next : HighFanState K :=
      {
        v := old.transition.z0
        x := old.transition.z1
        v_supported := old.transition.z0_supported
        x_supported := old.transition.z1_supported
        endpoints_ne := old.transition.endpoints_ne
        transition := T'
      }

    obtain ⟨p, q, gamma, hp, hq, hrange⟩ :=
      old.transition.exists_twoTet_continuousArc

    refine ⟨next, p, q, old.transition.witness, gamma,
      ?_, hp, ?_, old.transition.witness_mem, hrange⟩

    · exact FanReentryModeStep.fan_next old next rfl rfl

    · exact hq



/--
Under the fail-closed hypotheses, select an infinite high-fan
trajectory with a certified continuous two-tetrahedron-supported
path for every transition.

No geometric cycle obstruction is claimed.
-/
theorem ClosedTriangulationCore.exists_perpetual_geometric_highFan_trajectory
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hphi : 0 < PhiSupport K)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (start : HighFanState K) :
    ∃ states : Nat → HighFanState K,
      states 0 = start ∧
      ∀ n,
        ∃ (p q : triangulationTopologicalGeometricCarrier K)
          (tau : Tet)
          (gamma : Path p q),
          FanReentryModeStep K
            (.fan (states n)) (.fan (states (n + 1))) ∧
          p.1 =
            triangulationTopologicalGeometricEdgeMidpoint
              (states n).v (states n).x ∧
          q.1 =
            triangulationTopologicalGeometricEdgeMidpoint
              (states (n + 1)).v (states (n + 1)).x ∧
          tau ∈ K.tets ∧
          Set.range gamma ⊆
            (Subtype.val ⁻¹'
              triangulationTopologicalTetBody
                (states n).transition.leftTet) ∪
            (Subtype.val ⁻¹'
              triangulationTopologicalTetBody tau) := by
  classical

  have hconnected : ConnectedLinkClosedCore K :=
    connectedLinkClosedCore_of_topologicalThreeManifold
      K hcore hM

  have hlinks :
      ∀ u ∈ vertexSupport K, VertexLinkConnected K u :=
    hconnected.2

  have hconn : TetrahedronVertexOverlapConnected K :=
    hcore.tetrahedronVertexOverlapConnected_of_topologicalThreeManifold hM

  have hNoFour :
      ∀ u ∈ vertexSupport K, vertexDegree K u ≠ 4 := by
    rcases
        hcore.exists_topology_preserving_PhiSupport_descent_or_no_degree_four
          hlinks hconn hphi with
      hdescent | hno
    · exact (hNoDescent hdescent).elim
    · exact hno

  have hnext : ∀ old : HighFanState K,
      ∃ (next : HighFanState K)
        (p q : triangulationTopologicalGeometricCarrier K)
        (tau : Tet)
        (gamma : Path p q),
        FanReentryModeStep K (.fan old) (.fan next) ∧
        p.1 =
          triangulationTopologicalGeometricEdgeMidpoint old.v old.x ∧
        q.1 =
          triangulationTopologicalGeometricEdgeMidpoint next.v next.x ∧
        tau ∈ K.tets ∧
        Set.range gamma ⊆
          (Subtype.val ⁻¹'
            triangulationTopologicalTetBody old.transition.leftTet) ∪
          (Subtype.val ⁻¹'
            triangulationTopologicalTetBody tau) := by
    intro old
    exact hcore.exists_geometric_highFan_successor
      hM hlinks hNoFour hNoMove23 hNoDescent old

  let step : HighFanState K → HighFanState K :=
    fun old => Classical.choose (hnext old)

  have hstep : ∀ old : HighFanState K,
      ∃ (p q : triangulationTopologicalGeometricCarrier K)
        (tau : Tet)
        (gamma : Path p q),
        FanReentryModeStep K (.fan old) (.fan (step old)) ∧
        p.1 =
          triangulationTopologicalGeometricEdgeMidpoint old.v old.x ∧
        q.1 =
          triangulationTopologicalGeometricEdgeMidpoint
            (step old).v (step old).x ∧
        tau ∈ K.tets ∧
        Set.range gamma ⊆
          (Subtype.val ⁻¹'
            triangulationTopologicalTetBody old.transition.leftTet) ∪
          (Subtype.val ⁻¹'
            triangulationTopologicalTetBody tau) := by
    intro old
    exact Classical.choose_spec (hnext old)

  let states : Nat → HighFanState K :=
    fun n => Nat.rec start (fun _ old => step old) n

  refine ⟨states, ?_, ?_⟩
  · simp [states]
  · intro n
    simpa [states] using hstep (states n)


/--
Finite repetition of edge keys along a geometrically certified
high-fan trajectory.

Each intermediate step admits an actual continuous carrier
path supported in the union of two represented tetrahedra.
No cycle obstruction or filling-to-descent conclusion follows.
-/
theorem ClosedTriangulationCore.exists_recurrent_geometric_highFan_trajectory
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hphi : 0 < PhiSupport K)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (start : HighFanState K) :
    ∃ (states : Nat → HighFanState K) (i j : Nat),
      states 0 = start ∧
      i + 1 < j ∧
      j ≤ Fintype.card (SupportedEdgeState K) ∧
      (states i).edgeState = (states j).edgeState ∧
      ∀ n, i ≤ n → n < j →
        ∃ (p q : triangulationTopologicalGeometricCarrier K)
          (tau : Tet) (gamma : Path p q),
          FanReentryModeStep K
            (.fan (states n)) (.fan (states (n + 1))) ∧
          p.1 =
            triangulationTopologicalGeometricEdgeMidpoint
              (states n).v (states n).x ∧
          q.1 =
            triangulationTopologicalGeometricEdgeMidpoint
              (states (n + 1)).v (states (n + 1)).x ∧
          tau ∈ K.tets ∧
          Set.range gamma ⊆
            (Subtype.val ⁻¹'
              triangulationTopologicalTetBody
                (states n).transition.leftTet) ∪
            (Subtype.val ⁻¹'
              triangulationTopologicalTetBody tau) := by
  classical

  obtain ⟨states, hzero, hpaths⟩ :=
    hcore.exists_perpetual_geometric_highFan_trajectory
      hM hphi hNoMove23 hNoDescent start

  let N : Nat := Fintype.card (SupportedEdgeState K)
  let f : Nat → SupportedEdgeState K :=
    fun n => (states n).edgeState
  let S : Finset Nat := Finset.range (N + 1)
  let T : Finset (SupportedEdgeState K) := Finset.univ

  have hcard : T.card < S.card := by
    simp [T, S, N]

  have hmaps :
      Set.MapsTo f
        (↑S : Set Nat)
        (↑T : Set (SupportedEdgeState K)) := by
    intro n hn
    simp [T]

  obtain ⟨i, hiS, j, hjS, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := S) (t := T) hcard hmaps

  have hiBound : i ≤ N := by
    have hiLt : i < N + 1 := by
      simpa [S] using hiS
    omega

  have hjBound : j ≤ N := by
    have hjLt : j < N + 1 := by
      simpa [S] using hjS
    omega

  have hprogress :
      ∀ n, f (n + 1) ≠ f n := by
    intro n
    obtain ⟨p, q, tau, gamma,
      hstep, hp, hq, htau, hrange⟩ := hpaths n
    have hkey := hstep.fan_to_fan_canonicalEdgeKey_ne
    intro hEq
    apply hkey
    have hh :=
      congrArg (fun e : SupportedEdgeState K => e.key) hEq
    simpa [f] using hh

  rcases Nat.lt_or_gt_of_ne hij with hijlt | hjilt
  · have hgap : i + 1 < j := by
      by_contra hnot
      have hsucc : j = i + 1 := by omega
      subst j
      exact (hprogress i) heq.symm

    refine ⟨states, i, j, hzero, hgap, ?_, ?_, ?_⟩
    · simpa [N] using hjBound
    · simpa [f] using heq
    · intro n hin hnj
      exact hpaths n

  · have hgap : j + 1 < i := by
      by_contra hnot
      have hsucc : i = j + 1 := by omega
      subst i
      exact (hprogress j) heq

    refine ⟨states, j, i, hzero, hgap, ?_, ?_, ?_⟩
    · simpa [N] using hiBound
    · simpa [f] using heq.symm
    · intro n hin hnj
      exact hpaths n



/-- Canonical geometric midpoint of a high-fan central edge. -/
noncomputable def HighFanState.geometricMidpoint
    {K : Triangulation} (q : HighFanState K) :
    triangulationTopologicalGeometricCarrier K := by
  have hv : q.v ∈ q.transition.leftTet.verts := by
    apply (q.transition.leftTet_match q.v).2
    simp [Tet.verts]
  have hx : q.x ∈ q.transition.leftTet.verts := by
    apply (q.transition.leftTet_match q.x).2
    simp [Tet.verts]
  exact
    ⟨triangulationTopologicalGeometricEdgeMidpoint q.v q.x,
      triangulationTopologicalTetBody_subset_carrier
        K q.transition.leftTet_mem
        (triangulationTopologicalGeometricEdgeMidpoint_mem_tetBody
          hv hx)⟩

/-- Repetition of an unordered edge identifies its midpoint. -/
theorem HighFanState.geometricMidpoint_eq_of_edgeState_eq
    {K : Triangulation} (a b : HighFanState K)
    (h : a.edgeState = b.edgeState) :
    a.geometricMidpoint = b.geometricMidpoint := by
  apply Subtype.ext
  have hkey :
      canonicalEdgeKey a.v a.x =
        canonicalEdgeKey b.v b.x := by
    calc
      canonicalEdgeKey a.v a.x = a.edgeState.key :=
        a.edgeState_key.symm
      _ = b.edgeState.key :=
        congrArg SupportedEdgeState.key h
      _ = canonicalEdgeKey b.v b.x :=
        b.edgeState_key

  rcases
      (canonicalEdgeKey_eq_iff
        a.v a.x b.v b.x
        a.endpoints_ne b.endpoints_ne).1 hkey with
    ⟨hv, hx⟩ | ⟨hv, hx⟩

  · change
      triangulationTopologicalGeometricEdgeMidpoint a.v a.x =
        triangulationTopologicalGeometricEdgeMidpoint b.v b.x
    rw [hv, hx]

  · change
      triangulationTopologicalGeometricEdgeMidpoint a.v a.x =
        triangulationTopologicalGeometricEdgeMidpoint b.v b.x
    funext t
    simp only [triangulationTopologicalGeometricEdgeMidpoint_apply]
    rw [hv, hx]
    ac_rfl

/--
A path can be concatenated over the exact certified interval,
without asserting anything about steps outside that interval.
-/
theorem exists_bounded_geometricPath
    {K : Triangulation}
    (states : Nat → HighFanState K)
    (i j : Nat)
    (hij : i ≤ j)
    (hsteps :
      ∀ n, i ≤ n → n < j →
        ∃ (p q : triangulationTopologicalGeometricCarrier K)
          (tau : Tet) (gamma : Path p q),
          FanReentryModeStep K
            (.fan (states n))
            (.fan (states (n + 1))) ∧
          p.1 =
            triangulationTopologicalGeometricEdgeMidpoint
              (states n).v (states n).x ∧
          q.1 =
            triangulationTopologicalGeometricEdgeMidpoint
              (states (n + 1)).v
              (states (n + 1)).x ∧
          tau ∈ K.tets ∧
          Set.range gamma ⊆
            (Subtype.val ⁻¹'
              triangulationTopologicalTetBody
                (states n).transition.leftTet) ∪
            (Subtype.val ⁻¹'
              triangulationTopologicalTetBody tau)) :
    Nonempty
      (Path (states i).geometricMidpoint
        (states j).geometricMidpoint) := by
  classical

  have hpaths :
      ∀ k : Nat, i + k ≤ j →
        Nonempty
          (Path (states i).geometricMidpoint
            (states (i + k)).geometricMidpoint) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using
          (⟨Path.refl (states i).geometricMidpoint⟩ :
            Nonempty
              (Path (states i).geometricMidpoint
                (states i).geometricMidpoint))

    | succ k ih =>
        intro hk

        have hk0 : i + k ≤ j := by omega
        have hki : i ≤ i + k := by omega
        have hkj : i + k < j := by omega

        obtain ⟨priorPath⟩ := ih hk0

        obtain ⟨p, q, tau, gamma,
          _hlink, hp, hq, _htau, _hrange⟩ :=
          hsteps (i + k) hki hkj

        have hp' :
            p = (states (i + k)).geometricMidpoint :=
          Subtype.ext hp

        have hq' :
            q = (states (i + k + 1)).geometricMidpoint :=
          Subtype.ext hq

        subst p
        subst q

        have composed :
            Path (states i).geometricMidpoint
              (states (i + k + 1)).geometricMidpoint :=
          priorPath.trans gamma

        simpa only [Nat.add_succ] using
          (⟨composed⟩ :
            Nonempty
              (Path (states i).geometricMidpoint
                (states (i + k + 1)).geometricMidpoint))

  have hj : i + (j - i) = j := by omega

  have hpath := hpaths (j - i) (by omega)
  rw [hj] at hpath
  exact hpath

/--
A nonconsecutive return of the supported-edge key yields
an actual closed continuous carrier path.

No embeddedness, nonzero winding, or descent is asserted.
-/
theorem ClosedTriangulationCore.exists_closed_geometric_recurrence_loop
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hphi : 0 < PhiSupport K)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (start : HighFanState K) :
    ∃ (states : Nat → HighFanState K)
      (i j : Nat)
      (gamma : Path
        (states i).geometricMidpoint
        (states i).geometricMidpoint),
      states 0 = start ∧
      i + 1 < j ∧
      j ≤ Fintype.card (SupportedEdgeState K) ∧
      (states i).edgeState = (states j).edgeState := by
  classical

  obtain ⟨states, i, j,
    hzero, hgap, hbound, hkey, hsteps⟩ :=
    hcore.exists_recurrent_geometric_highFan_trajectory
      hM hphi hNoMove23 hNoDescent start

  obtain ⟨gamma⟩ :=
    exists_bounded_geometricPath
      states i j (by omega) hsteps

  have hmid :
      (states i).geometricMidpoint =
        (states j).geometricMidpoint :=
    HighFanState.geometricMidpoint_eq_of_edgeState_eq
      (states i) (states j) hkey

  rw [← hmid] at gamma

  exact ⟨states, i, j, gamma,
    hzero, hgap, hbound, hkey⟩


/--
The recurrent geometric loop is null-homotopic when the
actual carrier is simply connected.

This theorem does not assert that a null-homotopy provides
a topology-preserving combinatorial simplification.
-/
theorem ClosedTriangulationCore.exists_nullHomotopic_geometric_fan_loop
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hSC : TriangulationRealizationSimplyConnected K)
    (hphi : 0 < PhiSupport K)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (start : HighFanState K) :
    ∃ (states : Nat → HighFanState K)
      (i j : Nat)
      (gamma : Path
        (states i).geometricMidpoint
        (states i).geometricMidpoint),
      states 0 = start ∧
      i + 1 < j ∧
      j ≤ Fintype.card (SupportedEdgeState K) ∧
      (states i).edgeState = (states j).edgeState ∧
      Path.Homotopic gamma
        (Path.refl (states i).geometricMidpoint) := by
  classical
  obtain ⟨states, i, j, gamma,
      hzero, hgap, hbound, hkey⟩ :=
    hcore.exists_closed_geometric_recurrence_loop
      hM hphi hNoMove23 hNoDescent start

  letI : SimplyConnectedSpace
      (triangulationTopologicalGeometricCarrier K) := hSC

  have hnull :
      Path.Homotopic gamma
        (Path.refl (states i).geometricMidpoint) :=
    SimplyConnectedSpace.paths_homotopic
      gamma (Path.refl (states i).geometricMidpoint)

  exact ⟨states, i, j, gamma,
    hzero, hgap, hbound, hkey, hnull⟩


/--
A filling of any carrier loop has a finite dyadic grid labeling
whose labels for cells meeting at one point share a represented
tetrahedron.

No hNoHigh, descent, or no-reinjection assumption occurs.
-/
theorem CarrierLoopNullHomotopyData.exists_dyadic_common_coface_labelling
    {K : Triangulation}
    {x : triangulationTopologicalGeometricCarrier K}
    {loop : Path x x}
    (H : CarrierLoopNullHomotopyData K x loop)
    (m : Nat) :
    ∃ (N : Nat) (hN : 0 < N)
      (hD : 0 < N * 2 ^ m)
      (label : Fin (N * 2 ^ m) → Fin (N * 2 ^ m) → Nat),
      (∀ i j, label i j ∈ vertexSupport K) ∧
      (∀ i j z,
        z ∈ CarrierLoopNullHomotopyData.squareGridCell
          (N * 2 ^ m) hD i j →
        0 < (H.homotopy z).1 (label i j)) ∧
      ∀ S : Finset (Fin (N * 2 ^ m) × Fin (N * 2 ^ m)),
        (∃ z, ∀ ij ∈ S,
          z ∈ CarrierLoopNullHomotopyData.squareGridCell
            (N * 2 ^ m) hD ij.1 ij.2) →
        ∃ tau ∈ K.tets,
          ∀ ij ∈ S, label ij.1 ij.2 ∈ tau.verts := by
  classical
  obtain ⟨N, hN, hD, label, hsupport, hpositive⟩ :=
    H.exists_finite_squareGrid_dyadic_refinement_positiveCoordinate_labelling_probe m
  refine ⟨N, hN, hD, label, hsupport, hpositive, ?_⟩
  intro S hoverlap
  obtain ⟨z, hz⟩ := hoverlap
  have hspace :
      (H.homotopy z).1 ∈
        (triangulationTopologicalGeometricComplex K).space :=
    (H.homotopy z).2
  have hspaceUnion :
      (H.homotopy z).1 ∈
        ⋃ (tau : Tet) (_ : tau ∈ K.tets),
          triangulationTopologicalTetBody tau := by
    simpa only
      [triangulationTopologicalGeometricComplex_space_eq_tetrahedronUnion K]
      using hspace
  simp only [Set.mem_iUnion] at hspaceUnion
  obtain ⟨tau, htau, hbody⟩ := hspaceUnion
  refine ⟨tau, htau, ?_⟩
  intro ij hij
  have hpos :
      0 < (H.homotopy z).1 (label ij.1 ij.2) :=
    hpositive ij.1 ij.2 z (hz ij hij)
  by_contra hnot
  have hz0 :=
    triangulationTopologicalTetBody_coordinate_eq_zero_of_not_mem
      tau (label ij.1 ij.2) hnot hbody
  linarith

/--
The verified recurrent geometric fan loop has a finite
common-coface null-homotopy filling. High-edge reinjection
is permitted; no incompatible no-high assumption is used.
-/
theorem ClosedTriangulationCore.exists_highFan_common_coface_filling
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hSC : TriangulationRealizationSimplyConnected K)
    (hphi : 0 < PhiSupport K)
    (hNoMove23 : ¬ ∃ m : Move23Site, m.LegalIn K)
    (hNoDescent :
      ¬ ∃ K',
        ClosedTriangulationCore K' ∧
        PhiSupport K' < PhiSupport K ∧
        Nonempty
          (triangulationTopologicalGeometricCarrier K ≃ₜ
            triangulationTopologicalGeometricCarrier K'))
    (start : HighFanState K)
    (m : Nat) :
    ∃ (states : Nat → HighFanState K)
      (i j : Nat)
      (gamma : Path
        (states i).geometricMidpoint
        (states i).geometricMidpoint)
      (H : CarrierLoopNullHomotopyData K
        (states i).geometricMidpoint gamma)
      (N : Nat) (hN : 0 < N)
      (hD : 0 < N * 2 ^ m)
      (label : Fin (N * 2 ^ m) → Fin (N * 2 ^ m) → Nat),
      states 0 = start ∧
      i + 1 < j ∧
      j ≤ Fintype.card (SupportedEdgeState K) ∧
      (states i).edgeState = (states j).edgeState ∧
      (∀ a b, label a b ∈ vertexSupport K) ∧
      (∀ a b z,
        z ∈ CarrierLoopNullHomotopyData.squareGridCell
          (N * 2 ^ m) hD a b →
        0 < (H.homotopy z).1 (label a b)) ∧
      ∀ S : Finset (Fin (N * 2 ^ m) × Fin (N * 2 ^ m)),
        (∃ z, ∀ ab ∈ S,
          z ∈ CarrierLoopNullHomotopyData.squareGridCell
            (N * 2 ^ m) hD ab.1 ab.2) →
        ∃ tau ∈ K.tets,
          ∀ ab ∈ S, label ab.1 ab.2 ∈ tau.verts := by
  classical
  obtain ⟨states, i, j, gamma,
    hzero, hgap, hbound, hreturn⟩ :=
    hcore.exists_closed_geometric_recurrence_loop
      hM hphi hNoMove23 hNoDescent start

  letI : SimplyConnectedSpace
      (triangulationTopologicalGeometricCarrier K) := hSC

  obtain ⟨H⟩ :=
    exists_carrierLoopNullHomotopyData hSC gamma

  obtain ⟨N, hN, hD, label,
    hsupport, hpositive, hcommon⟩ :=
    H.exists_dyadic_common_coface_labelling m

  exact ⟨states, i, j, gamma, H,
    N, hN, hD, label,
    hzero, hgap, hbound, hreturn,
    hsupport, hpositive, hcommon⟩

end Poincare

#print axioms Poincare.CarrierLoopNullHomotopyData.exists_dyadic_common_coface_labelling
#print axioms Poincare.ClosedTriangulationCore.exists_highFan_common_coface_filling
