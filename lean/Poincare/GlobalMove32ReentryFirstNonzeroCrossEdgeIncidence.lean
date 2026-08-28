import Poincare.GlobalMove32ReentryFirstNonzeroEarIncidence
import Poincare.GlobalRepresentedEdgeIncidenceSplit

namespace Poincare

/-- A genuine one-sided first-ear escape carries one of the four anchor cross
edges `bd`, `be`, `ad`, or `ae`.  Since that edge is represented by the escape
tetrahedron, its closed-core tetrahedron incidence is exactly three or at
least four.  This theorem deliberately stops before constructing a new
Move32 site or claiming source-face absence. -/
theorem ClosedTriangulationCore.exists_crossEdge_incidenceSplit_of_move32_oneSided_sourceEndpoint_escape
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move32Site)
    (hrealized : s.RealizedIn K)
    {rho : Tet}
    (hrho : rho ∈ K.tets)
    {q : Nat}
    (hqRho : q ∈ rho.verts)
    (hsource : q = s.b ∨ q = s.a)
    (honeSided :
      (s.d ∈ rho.verts ∧ s.e ∉ rho.verts) ∨
      (s.e ∈ rho.verts ∧ s.d ∉ rho.verts)) :
    ∃ v x : Nat,
      ((v = s.b ∧ x = s.d) ∨
        (v = s.b ∧ x = s.e) ∨
        (v = s.a ∧ x = s.d) ∨
        (v = s.a ∧ x = s.e)) ∧
      v ∈ rho.verts ∧
      x ∈ rho.verts ∧
      ((K.tets.filter
          (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length = 3 ∨
        4 ≤ (K.tets.filter
          (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length) := by
  classical

  have hdistinct := hcore.move32Site_distinct s hrealized

  have hbD : s.b ≠ s.d := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have hbE : s.b ≠ s.e := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have haD : s.a ≠ s.d := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have haE : s.a ≠ s.e := by
    have h := hdistinct
    simp [List.nodup_cons] at h
    aesop

  have edgeSplit
      (v x : Nat)
      (hvx : v ≠ x)
      (hv : v ∈ rho.verts)
      (hx : x ∈ rho.verts) :
      (K.tets.filter
          (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length = 3 ∨
        4 ≤ (K.tets.filter
          (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts)).length := by
    apply hcore.edgeIncidence_eq_three_or_four_le_of_pos v x hvx
    have hm :
        rho ∈ K.tets.filter
          (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts) := by
      simp [hrho, hv, hx]
    have hne :
        K.tets.filter
          (fun tau => v ∈ tau.verts ∧ x ∈ tau.verts) ≠ [] := by
      intro hnil
      rw [hnil] at hm
      simp at hm
    exact List.length_pos.mpr hne

  rcases hsource with hqB | hqA

  · subst q
    rcases honeSided with hD | hE
    · refine ⟨s.b, s.d, ?_, hqRho, hD.1, ?_⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact edgeSplit s.b s.d hbD hqRho hD.1
    · refine ⟨s.b, s.e, ?_, hqRho, hE.1, ?_⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact edgeSplit s.b s.e hbE hqRho hE.1

  · subst q
    rcases honeSided with hD | hE
    · refine ⟨s.a, s.d, ?_, hqRho, hD.1, ?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact edgeSplit s.a s.d haD hqRho hD.1
    · refine ⟨s.a, s.e, ?_, hqRho, hE.1, ?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact edgeSplit s.a s.e haE hqRho hE.1

end Poincare
