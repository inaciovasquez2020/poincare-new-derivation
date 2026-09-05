import Poincare.GlobalFanReentryModeContinuation

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

end Poincare
