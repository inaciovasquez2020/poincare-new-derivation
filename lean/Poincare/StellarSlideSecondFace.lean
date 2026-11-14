import Poincare.StellarSlideFirstReplacement

namespace Poincare

/-- In a closed core, once the two adjacent tetrahedra over a face are
explicitly listed, no tetrahedron in the remaining list contains that face.
This is the face-absence obligation needed for the second stellar-slide move. -/
theorem Move41Site.slide_second_rest_face_absent
    (s : Move41Site) (f : Nat) (rest : List Tet)
    (hcore : ClosedTriangulationCore
      ({ tets := s.targetTet :: (⟨s.a, s.b, s.c, f⟩ : Tet) :: rest } :
        Triangulation)) :
    ∀ τ ∈ rest, ¬ (s.a ∈ τ.verts ∧ s.b ∈ τ.verts ∧ s.c ∈ τ.verts) := by
  have habc : [s.a, s.b, s.c].Nodup := by
    have hd := s.distinct
    simp at hd ⊢
    aesop
  have hcount :
      ((s.targetTet :: (⟨s.a, s.b, s.c, f⟩ : Tet) :: rest).filter
        (fun τ => s.a ∈ τ.verts ∧ s.b ∈ τ.verts ∧ s.c ∈ τ.verts)).length = 2 := by
    exact hcore.2.2 s.a s.b s.c habc
      ⟨s.targetTet, by simp, by simp [Move41Site.targetTet, Tet.verts]⟩
  have hzero :
      (rest.filter (fun τ => s.a ∈ τ.verts ∧
        s.b ∈ τ.verts ∧ s.c ∈ τ.verts)).length = 0 := by
    simp [Move41Site.targetTet, Tet.verts] at hcount
    omega
  have hnil :
      rest.filter (fun τ => s.a ∈ τ.verts ∧
        s.b ∈ τ.verts ∧ s.c ∈ τ.verts) = [] := by
    cases h : rest.filter (fun τ => s.a ∈ τ.verts ∧
      s.b ∈ τ.verts ∧ s.c ∈ τ.verts) with
    | nil => exact h
    | cons τ tail => simp [h] at hzero
  intro τ hτ habcτ
  have hmem :
      τ ∈ rest.filter (fun σ => s.a ∈ σ.verts ∧
        s.b ∈ σ.verts ∧ s.c ∈ σ.verts) := by
    simp [hτ, habcτ]
  rw [hnil] at hmem
  cases hmem

end Poincare
