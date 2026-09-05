import Poincare.GlobalHighEdgeToFanState
import Poincare.GlobalFanChordTransition
import Poincare.GlobalMove32SharedEdgeThreeTetSaturation
import Poincare.Move23UnchangedOverlap

namespace Poincare

/-- Continue a fan-chord transition without assuming that source-obstruction
high edges are absent.  Any such high edge is immediately rebuilt as its own
high-fan state.  The only remaining one-step exits are a legal `2-3` move,
strict topology-preserving `PhiSupport` descent, witnessed source-face reentry,
or another high-fan state. -/
theorem ClosedTriangulationCore.FanChordTransition.continue_reinjectHigh
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (hM : TriangulationRealizationIsClosedConnectedTopologicalThreeManifold K)
    (hlinks :
      ∀ v ∈ vertexSupport K,
        VertexLinkConnected K v)
    (hconn : TetrahedronVertexOverlapConnected K)
    (hNoFour :
      ∀ v ∈ vertexSupport K,
        vertexDegree K v ≠ 4)
    {v x : Nat}
    (T : FanChordTransition K v x) :
    (∃ m : Move23Site, m.LegalIn K) ∨
    (∃ K',
      ClosedTriangulationCore K' ∧
      PhiSupport K' < PhiSupport K ∧
      Nonempty
        (triangulationTopologicalGeometricCarrier K ≃ₜ
          triangulationTopologicalGeometricCarrier K')) ∨
    (∃ s s' : Move32Site,
      s.RealizedIn K ∧
      s.SharedEdgeExactlyThree K ∧
      Move32SourceFaceWitnessedReentry K s s') ∨
    Nonempty (HighFanState K) := by
  rcases
      ClosedTriangulationCore.FanChordTransition.continue_witnessed
        hcore hM hlinks hconn hNoFour T with
    hmove23 | hdescent | hhigh | hreentry | hnext

  · exact Or.inl hmove23

  · exact Or.inr (Or.inl hdescent)

  · obtain ⟨p, q, sigma, hpq, hsigma, hp, hq, hinc⟩ := hhigh
    have hinc' :
        4 ≤ (K.tets.filter
          (fun gamma => p ∈ gamma.verts ∧ q ∈ gamma.verts)).length := by
      simpa using hinc

    rcases
        hcore.exists_legal_move23_or_highFanState_of_edgeIncidence_four_le
          hM hpq hsigma hp hq hinc' with
      hmove23 | hstate

    · exact Or.inl hmove23
    · exact Or.inr (Or.inr (Or.inr hstate))

  · exact Or.inr (Or.inr (Or.inl hreentry))

  · obtain ⟨T'⟩ := hnext
    exact
      Or.inr
        (Or.inr
          (Or.inr
            ⟨{
              v := T.z0
              x := T.z1
              v_supported := T.z0_supported
              x_supported := T.z1_supported
              endpoints_ne := T.endpoints_ne
              transition := T'
            }⟩))

/-- The shared-face edge `(a,b)` loses exactly one tetrahedron under a legal
`2-3` move.  In particular, incidence four becomes incidence three.  This is
the count needed to turn a four-valent high-fan central edge into the first
`3-2` candidate of the descent block. -/
theorem Move23Site.replace_ab_edgeIncidence_three_of_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4 :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts)).length = 4) :
    ((m.replace K).tets.filter (fun tau =>
      m.a ∈ tau.verts ∧ m.b ∈ tau.verts)).length = 3 := by
  let p : Tet → Prop := fun tau =>
    m.a ∈ tau.verts ∧ m.b ∈ tau.verts
  have hinvariant :
      ∀ tau sigma,
        SameTetVertices tau sigma →
        (p tau ↔ p sigma) := by
    intro tau sigma hsame
    constructor
    · intro h
      exact ⟨(hsame m.a).1 h.1, (hsame m.b).1 h.2⟩
    · intro h
      exact ⟨(hsame m.a).2 h.1, (hsame m.b).2 h.2⟩
  have hsplit :=
    hcore.move23Site_unchanged_filter_length_add_local_eq
      m hlegal p hinvariant
  have hlocal :
      ([m.leftTet, m.rightTet].filter p).length = 2 := by
    simp [p, Move23Site.leftTet, Move23Site.rightTet, Tet.verts]
  have htwo :
      ((m.unchangedTets K).filter (fun tau =>
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts)).length = 2 := by
    dsimp [p] at hsplit
    rw [hlocal] at hsplit
    omega
  rw [m.replace_tets_eq K]
  have hd := m.distinct
  simp at hd
  simpa [List.filter_cons, Move23Site.newTet₀, Move23Site.newTet₁,
    Move23Site.newTet₂, Tet.verts, hd, Ne.symm] using congrArg Nat.succ htwo

/-- Incidence four on the shared-face edge `(a,b)` therefore yields a realized
exact-three `Move32Site` on that same edge after the legal `2-3`.  This is the
first geometric object needed to turn the four-fan legal-move branch into a
`2-3,3-2,3-2` descent block. -/
theorem Move23Site.exists_move32_candidate_on_ab_after_incidence_four
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hinc4 :
      (K.tets.filter (fun tau =>
        m.a ∈ tau.verts ∧ m.b ∈ tau.verts)).length = 4) :
    ∃ s : Move32Site,
      s.d = m.a ∧
      s.e = m.b ∧
      s.RealizedIn (m.replace K) ∧
      s.SharedEdgeExactlyThree (m.replace K) := by
  have hcore' : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hthree :=
    m.replace_ab_edgeIncidence_three_of_incidence_four hcore hlegal hinc4
  have hab : m.a ≠ m.b := by
    have hd := m.distinct
    simp at hd
    aesop
  exact
    hcore'.exists_move32Site_realizedIn_of_edgeIncidence_three
      m.a m.b hab hthree

/-- Any realized exact-three candidate on the post-`2-3` edge `(a,b)` has both
new-edge endpoints `m.d,m.e` among its three source-face vertices.  The inserted
tetrahedron `newTet₀ = {a,b,d,e}` is one of the three saturated edge targets,
so its two vertices off the shared edge must be source vertices of the
candidate. -/
theorem Move23Site.move32_candidate_sourceFace_contains_newEdgeEndpoints
    {K : Triangulation} (m : Move23Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (s : Move32Site)
    (hsd : s.d = m.a)
    (hse : s.e = m.b)
    (hrealized : s.RealizedIn (m.replace K))
    (hthree : s.SharedEdgeExactlyThree (m.replace K)) :
    m.d ∈ [s.a, s.b, s.c] ∧
      m.e ∈ [s.a, s.b, s.c] := by
  have hcore' : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hnew : m.newTet₀ ∈ (m.replace K).tets := by
    rw [m.replace_tets_eq K]
    simp
  have hsdNew : s.d ∈ m.newTet₀.verts := by
    rw [hsd]
    simp [Move23Site.newTet₀, Tet.verts]
  have hseNew : s.e ∈ m.newTet₀.verts := by
    rw [hse]
    simp [Move23Site.newTet₀, Tet.verts]
  have htarget :=
    hcore'.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
      s hrealized hthree hnew hsdNew hseNew
  have hm := m.distinct
  simp at hm
  rcases htarget with h0 | h1 | h2
  · have hmd := (h0 m.d).1 (by
      simp [Move23Site.newTet₀, Tet.verts])
    have hme := (h0 m.e).1 (by
      simp [Move23Site.newTet₀, Tet.verts])
    simp [Move32Site.targetTet₀, Tet.verts, hsd, hse] at hmd hme
    simp only [List.mem_cons, List.mem_singleton]
    aesop
  · have hmd := (h1 m.d).1 (by
      simp [Move23Site.newTet₀, Tet.verts])
    have hme := (h1 m.e).1 (by
      simp [Move23Site.newTet₀, Tet.verts])
    simp [Move32Site.targetTet₁, Tet.verts, hsd, hse] at hmd hme
    simp only [List.mem_cons, List.mem_singleton]
    aesop
  · have hmd := (h2 m.d).1 (by
      simp [Move23Site.newTet₀, Tet.verts])
    have hme := (h2 m.e).1 (by
      simp [Move23Site.newTet₀, Tet.verts])
    simp [Move32Site.targetTet₂, Tet.verts, hsd, hse] at hmd hme
    simp only [List.mem_cons, List.mem_singleton]
    aesop

end Poincare
