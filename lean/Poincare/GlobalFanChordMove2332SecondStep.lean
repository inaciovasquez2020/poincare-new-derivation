import Poincare.GlobalFanReentryModeContinuation
import Poincare.Move2332LocalEscapeCriterion

namespace Poincare

/-- The second shared-face edge `(a,c)` obeys the same local count as `(a,b)`:
a legal `2-3` move lowers incidence four to incidence three.  This is the
numerical prerequisite for the second `3-2` in the Move2332 descent block. -/
theorem Move23Site.replace_ac_edgeIncidence_three_of_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4 :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4) :
    ((m.replace K).tets.filter (fun tau =>
      m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 3 := by
  let p : Tet → Prop := fun tau =>
    m.a ∈ tau.verts ∧ m.c ∈ tau.verts
  have hinvariant :
      ∀ tau sigma,
        SameTetVertices tau sigma →
        (p tau ↔ p sigma) := by
    intro tau sigma hsame
    constructor
    · intro h
      exact ⟨(hsame m.a).1 h.1, (hsame m.c).1 h.2⟩
    · intro h
      exact ⟨(hsame m.a).2 h.1, (hsame m.c).2 h.2⟩
  have hsplit :=
    hcore.move23Site_unchanged_filter_length_add_local_eq
      m hlegal p hinvariant
  have hlocal :
      ([m.leftTet, m.rightTet].filter p).length = 2 := by
    simp [p, Move23Site.leftTet, Move23Site.rightTet, Tet.verts]
  have htwo :
      ((m.unchangedTets K).filter (fun tau =>
        m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 2 := by
    dsimp [p] at hsplit
    rw [hlocal] at hsplit
    omega
  rw [m.replace_tets_eq K]
  have hd := m.distinct
  simp at hd
  simpa [List.filter_cons, Move23Site.newTet₀, Move23Site.newTet₁,
    Move23Site.newTet₂, Tet.verts, hd, Ne.symm] using congrArg Nat.succ htwo

/-- After the first legal `3-2` on `(m.a,m.b)`, the other shared-face edge
`(m.a,m.c)` keeps incidence three, provided it started with incidence four
before the original legal `2-3`.  The first `3-2` local target and source
tetrahedra do not meet that edge because `m.c` is absent from its source face. -/
theorem Move23Site.first_move32_preserves_ac_edgeIncidence_three
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4ac :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4)
    (hsd : s.d = m.a)
    (hse : s.e = m.b)
    (hslegal : s.LegalIn (m.replace K))
    (hnotc : m.c ∉ [s.a, s.b, s.c]) :
    ((s.replace (m.replace K)).tets.filter (fun tau =>
      m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 3 := by
  have hcore' : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hthree :=
    m.replace_ac_edgeIncidence_three_of_incidence_four hcore hlegal hinc4ac
  let p : Tet → Prop := fun tau =>
    m.a ∈ tau.verts ∧ m.c ∈ tau.verts
  have hinvariant :
      ∀ tau sigma,
        SameTetVertices tau sigma →
        (p tau ↔ p sigma) := by
    intro tau sigma hsame
    constructor
    · intro h
      exact ⟨(hsame m.a).1 h.1, (hsame m.c).1 h.2⟩
    · intro h
      exact ⟨(hsame m.a).2 h.1, (hsame m.c).2 h.2⟩
  have hsplit :=
    hcore'.move32Site_unchanged_filter_length_add_local_eq
      s hslegal p hinvariant
  have hm := m.distinct
  have hfive := hcore'.move32Site_distinct s hslegal.1
  simp at hm hfive hnotc
  have ht0 : ¬ p s.targetTet₀ := by
    simp [p, Move32Site.targetTet₀, Tet.verts, hsd, hse]
    aesop
  have ht1 : ¬ p s.targetTet₁ := by
    simp [p, Move32Site.targetTet₁, Tet.verts, hsd, hse]
    aesop
  have ht2 : ¬ p s.targetTet₂ := by
    simp [p, Move32Site.targetTet₂, Tet.verts, hsd, hse]
    aesop
  have hu :
      ((s.unchangedTets (m.replace K)).filter p).length = 3 := by
    have hlocal :
        ([s.targetTet₀, s.targetTet₁, s.targetTet₂].filter p).length = 0 := by
      simp [ht0, ht1, ht2]
    rw [hlocal] at hsplit
    dsimp [p] at hsplit
    rw [hthree] at hsplit
    omega
  have hs0 : ¬ p s.sourceTet₀ := by
    simp [p, Move32Site.sourceTet₀, Tet.verts, hsd, hse]
    aesop
  have hs1 : ¬ p s.sourceTet₁ := by
    simp [p, Move32Site.sourceTet₁, Tet.verts, hsd, hse]
    aesop
  rw [s.replace_tets_eq]
  change
    ((s.sourceTet₀ :: s.sourceTet₁ :: s.unchangedTets (m.replace K)).filter p).length = 3
  simp [List.filter_cons, hs0, hs1, hu]

/-- The preserved incidence-three edge `(m.a,m.c)` therefore determines a
realized exact-three `Move32Site` after the first legal `3-2`. -/
theorem Move23Site.exists_second_move32_candidate_on_ac
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4ac :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4)
    (hsd : s.d = m.a)
    (hse : s.e = m.b)
    (hslegal : s.LegalIn (m.replace K))
    (hnotc : m.c ∉ [s.a, s.b, s.c]) :
    ∃ t : Move32Site,
      t.d = m.a ∧
      t.e = m.c ∧
      t.RealizedIn (s.replace (m.replace K)) ∧
      t.SharedEdgeExactlyThree (s.replace (m.replace K)) := by
  have hcore' : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hcore'' : ClosedTriangulationCore (s.replace (m.replace K)) :=
    hcore'.move32Site_replace_closedCore s hslegal
  have hthree :=
    m.first_move32_preserves_ac_edgeIncidence_three
      s hcore hlegal hinc4ac hsd hse hslegal hnotc
  have hac : m.a ≠ m.c := by
    have hd := m.distinct
    simp at hd
    aesop
  exact
    hcore''.exists_move32Site_realizedIn_of_edgeIncidence_three
      m.a m.c hac hthree

/-- Once the first legal `3-2` has exposed the second exact-three edge, there
are only two possibilities: the second source face is absent and the full
`2-3,3-2,3-2` block gives strict topology-preserving `PhiSupport` descent, or
that second source face is represented and is returned explicitly as the
remaining obstruction. -/
theorem Move23Site.exists_move2332_descent_or_second_sourceFace_obstruction
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4ac :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4)
    (hsd : s.d = m.a)
    (hse : s.e = m.b)
    (hslegal : s.LegalIn (m.replace K))
    (hnotc : m.c ∉ [s.a, s.b, s.c]) :
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    ∃ t : Move32Site,
      t.d = m.a ∧
      t.e = m.c ∧
      t.RealizedIn (s.replace (m.replace K)) ∧
      t.SharedEdgeExactlyThree (s.replace (m.replace K)) ∧
      ∃ tau ∈ (s.replace (m.replace K)).tets,
        t.a ∈ tau.verts ∧
        t.b ∈ tau.verts ∧
        t.c ∈ tau.verts := by
  classical
  obtain ⟨t, htd, hte, htrealized, htthree⟩ :=
    m.exists_second_move32_candidate_on_ac
      s hcore hlegal hinc4ac hsd hse hslegal hnotc
  by_cases habsent : t.SourceFaceAbsent (s.replace (m.replace K))
  · have hcore1 : ClosedTriangulationCore (m.replace K) :=
      hcore.move23Site_replace_closedCore m hlegal
    have hcore2 : ClosedTriangulationCore (s.replace (m.replace K)) :=
      hcore1.move32Site_replace_closedCore s hslegal
    have htlegal : t.LegalIn (s.replace (m.replace K)) :=
      ⟨htrealized, htthree, habsent⟩
    have hcore3 :
        ClosedTriangulationCore
          (t.replace (s.replace (m.replace K))) :=
      hcore2.move32Site_replace_closedCore t htlegal
    have hminus4 :=
      move2332Block_PhiSupport_add_four_eq
        hcore m hlegal s hslegal hcore1 t htlegal hcore2 hcore3
    have hlt :
        PhiSupport (t.replace (s.replace (m.replace K))) < PhiSupport K := by
      omega
    refine Or.inl ⟨t.replace (s.replace (m.replace K)), hcore3, hlt, ?_⟩
    exact ⟨(hcore.move23GeometricCarrierHomeomorph m hlegal).trans
      ((hcore1.move32GeometricCarrierHomeomorph s hslegal).trans
        (hcore2.move32GeometricCarrierHomeomorph t htlegal))⟩
  · rw [Move32Site.SourceFaceAbsent] at habsent
    push_neg at habsent
    exact Or.inr ⟨t, htd, hte, htrealized, htthree, habsent⟩

/-- Incidence four on both old shared-face edges `(a,b)` and `(a,c)` removes
all caller-supplied Move32 data.  The first exact-three site is constructed and
proved legal automatically; the second step then gives either strict
homeomorphism-preserving `PhiSupport` descent or the explicit second source-face
obstruction. -/
theorem Move23Site.exists_move2332_descent_or_second_sourceFace_obstruction_of_ab_ac_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4ab :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts)).length = 4)
    (hinc4ac :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.c ∈ tau.verts)).length = 4) :
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    ∃ s t : Move32Site,
      s.d = m.a ∧
      s.e = m.b ∧
      s.LegalIn (m.replace K) ∧
      t.d = m.a ∧
      t.e = m.c ∧
      t.RealizedIn (s.replace (m.replace K)) ∧
      t.SharedEdgeExactlyThree (s.replace (m.replace K)) ∧
      ∃ tau ∈ (s.replace (m.replace K)).tets,
        t.a ∈ tau.verts ∧
        t.b ∈ tau.verts ∧
        t.c ∈ tau.verts := by
  obtain ⟨s, hsd, hse, hslegal⟩ :=
    m.exists_legal_move32_on_ab_after_incidence_four
      hcore hlegal hinc4ab
  have hnotc :=
    m.move32_candidate_sourceFace_not_contains_oldThird
      hcore hlegal s hsd hse hslegal.1
  rcases
      m.exists_move2332_descent_or_second_sourceFace_obstruction
        s hcore hlegal hinc4ac hsd hse hslegal hnotc with
    hdescent | hobstruction
  · exact Or.inl hdescent
  · obtain ⟨t, htd, hte, htrealized, htthree, hobstruction⟩ := hobstruction
    exact
      Or.inr
        ⟨s, t, hsd, hse, hslegal,
          htd, hte, htrealized, htthree, hobstruction⟩

/-- The honest three-manifold and tetrahedron-overlap-connectedness hypotheses
survive the legal `2-3,3-2` prefix.  This removes the topological transport
part of the second-source-face classification boundary. -/
theorem Move23Site.first_move32_prefix_topological_package
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hM :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlegal : m.LegalIn K)
    (hslegal : s.LegalIn (m.replace K)) :
    TriangulationRealizationIsClosedConnectedTopologicalThreeManifold
        (s.replace (m.replace K)) ∧
      TetrahedronVertexOverlapConnected
        (s.replace (m.replace K)) := by
  have hcore1 : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hcore2 : ClosedTriangulationCore (s.replace (m.replace K)) :=
    hcore1.move32Site_replace_closedCore s hslegal
  have hM1 :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold
        (m.replace K) :=
    triangulationRealizationIsClosedConnectedTopologicalThreeManifold_of_homeomorph
      (hcore.move23GeometricCarrierHomeomorph m hlegal) hM
  have hM2 :
      TriangulationRealizationIsClosedConnectedTopologicalThreeManifold
        (s.replace (m.replace K)) :=
    triangulationRealizationIsClosedConnectedTopologicalThreeManifold_of_homeomorph
      (hcore1.move32GeometricCarrierHomeomorph s hslegal) hM1
  exact
    ⟨hM2,
      hcore2.tetrahedronVertexOverlapConnected_of_topologicalThreeManifold hM2⟩

end Poincare
