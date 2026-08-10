import Poincare.Move23FaceIncidenceTable
import Poincare.Move23UnchangedOverlap

namespace Poincare

/-- The `2-3` replacement preserves the two simplicial-complex parts of the
closed-core condition: every tetrahedron is nondegenerate and no two listed
tetrahedra have the same vertex set.  Face incidence is handled separately. -/
theorem ClosedTriangulationCore.move23Site_replace_simple
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (s : Move23Site)
    (hlegal : s.LegalIn K) :
    (∀ tau ∈ (s.replace K).tets, tau.verts.Nodup) ∧
      (s.replace K).tets.Pairwise
        (fun tau sigma => ¬ SameTetVertices tau sigma) := by
  have hdata := hcore.move23Site_simpleBistellarData s hlegal
  have hnew0 : s.newTet₀.verts.Nodup := hdata.2.2.2.2.2.1
  have hnew1 : s.newTet₁.verts.Nodup := hdata.2.2.2.2.2.2.1
  have hnew2 : s.newTet₂.verts.Nodup := hdata.2.2.2.2.2.2.2
  have hunchangedNodup :
      ∀ tau ∈ s.unchangedTets K, tau.verts.Nodup := by
    intro tau htau
    exact hcore.1 tau (hcore.move23Site_mem_unchangedTets s hlegal htau).1
  have hUsub : List.Sublist (s.unchangedTets K) K.tets := by
    exact (eraseFirstSameTet_sublist s.rightTet
      (eraseFirstSameTet s.leftTet K.tets)).trans
        (eraseFirstSameTet_sublist s.leftTet K.tets)
  have hUpair : (s.unchangedTets K).Pairwise
      (fun tau sigma => ¬ SameTetVertices tau sigma) :=
    hcore.2.1.sublist hUsub
  have hnew01 : ¬ SameTetVertices s.newTet₀ s.newTet₁ := by
    intro h
    have hb : s.b ∈ s.newTet₁.verts :=
      (h s.b).1 (by simp [Move23Site.newTet₀, Tet.verts])
    have hd := s.distinct
    simp [Move23Site.newTet₁, Tet.verts] at hb
    simp at hd
    aesop
  have hnew02 : ¬ SameTetVertices s.newTet₀ s.newTet₂ := by
    intro h
    have ha : s.a ∈ s.newTet₂.verts :=
      (h s.a).1 (by simp [Move23Site.newTet₀, Tet.verts])
    have hd := s.distinct
    simp [Move23Site.newTet₂, Tet.verts] at ha
    simp at hd
    aesop
  have hnew12 : ¬ SameTetVertices s.newTet₁ s.newTet₂ := by
    intro h
    have ha : s.a ∈ s.newTet₂.verts :=
      (h s.a).1 (by simp [Move23Site.newTet₁, Tet.verts])
    have hd := s.distinct
    simp [Move23Site.newTet₂, Tet.verts] at ha
    simp at hd
    aesop
  have hnewU : ∀ n ∈ [s.newTet₀, s.newTet₁, s.newTet₂],
      ∀ tau ∈ s.unchangedTets K, ¬ SameTetVertices n tau := by
    intro n hn tau htau hsame
    have htauK := (hcore.move23Site_mem_unchangedTets s hlegal htau).1
    apply hlegal.2.2 tau htauK
    constructor
    · exact (hsame s.d).1 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl <;>
          simp [Move23Site.newTet₀, Move23Site.newTet₁,
            Move23Site.newTet₂, Tet.verts])
    · exact (hsame s.e).1 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl <;>
          simp [Move23Site.newTet₀, Move23Site.newTet₁,
            Move23Site.newTet₂, Tet.verts])
  constructor
  · intro tau htau
    rw [s.replace_tets_eq K] at htau
    simp only [List.mem_cons] at htau
    rcases htau with rfl | rfl | rfl | htau
    · exact hnew0
    · exact hnew1
    · exact hnew2
    · exact hunchangedNodup tau htau
  · rw [s.replace_tets_eq K]
    simp only [List.pairwise_cons, List.mem_cons]
    refine ⟨?_, ?_, ?_, hUpair⟩
    · intro tau htau
      rcases htau with rfl | rfl | htau
      · exact hnew01
      · exact hnew02
      · exact hnewU s.newTet₀ (by simp) tau htau
    · intro tau htau
      rcases htau with rfl | htau
      · exact hnew12
      · exact hnewU s.newTet₁ (by simp) tau htau
    · exact fun tau htau => hnewU s.newTet₂ (by simp) tau htau

end Poincare
