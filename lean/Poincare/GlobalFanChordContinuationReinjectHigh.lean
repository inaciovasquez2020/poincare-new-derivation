import Poincare.GlobalHighEdgeToFanState
import Poincare.GlobalFanChordTransition
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

end Poincare
