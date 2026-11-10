import Poincare.HeadStellarNormalForm

namespace Poincare

/-- Pairwise distinctness of the four abstract stellar source tetrahedron
vertex sets follows from the five-vertex distinctness of the 4→1 site;
this does not require a closed manifold. -/
theorem Move41Site.sourceTets_pairwise_of_distinct (s : Move41Site) :
    s.sourceTets.Pairwise (fun τ σ => ¬ SameTetVertices τ σ) := by
  have hd := s.distinct
  simp [Move41Site.sourceTets, Move41Site.sourceTet₀,
    Move41Site.sourceTet₁, Move41Site.sourceTet₂,
    Move41Site.sourceTet₃] at hd ⊢
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro h
    have hx := (h s.c).1 (by simp [Tet.verts])
    simp [Tet.verts] at hx
    aesop
  · intro h
    have hx := (h s.b).1 (by simp [Tet.verts])
    simp [Tet.verts] at hx
    aesop
  · intro h
    have hx := (h s.a).1 (by simp [Tet.verts])
    simp [Tet.verts] at hx
    aesop
  · intro h
    have hx := (h s.b).1 (by simp [Tet.verts])
    simp [Tet.verts] at hx
    aesop
  · intro h
    have hx := (h s.a).1 (by simp [Tet.verts])
    simp [Tet.verts] at hx
    aesop
  · intro h
    have hx := (h s.a).1 (by simp [Tet.verts])
    simp [Tet.verts] at hx
    aesop

/-- The fresh head subdivision preserves the first two conditions of
`ClosedTriangulationCore`: nondegenerate tetrahedra and uniqueness of
represented vertex sets. The remaining triangular-face incidence condition
is deliberately *not* assumed or concluded. -/
theorem Move41Site.headStellar_simple
    (s : Move41Site) (rest : List Tet)
    (hcore : ClosedTriangulationCore
      ({ tets := s.targetTet :: rest } : Triangulation))
    (hfresh : ∀ τ ∈ rest, s.e ∉ τ.verts) :
    (∀ τ ∈ (s.headStellar rest).tets, τ.verts.Nodup) ∧
      (s.headStellar rest).tets.Pairwise
        (fun τ σ => ¬ SameTetVertices τ σ) := by
  have hfour (i : Fin 4) :
      (match i with
        | ⟨0, _⟩ => s.sourceTet₀
        | ⟨1, _⟩ => s.sourceTet₁
        | ⟨2, _⟩ => s.sourceTet₂
        | _ => s.sourceTet₃).verts.Nodup := by
    have hd := s.distinct
    fin_cases i <;>
      simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
        Move41Site.sourceTet₂, Move41Site.sourceTet₃,
        Tet.verts] at hd ⊢ <;> aesop
  have h0 : s.sourceTet₀.verts.Nodup := by simpa using hfour 0
  have h1 : s.sourceTet₁.verts.Nodup := by simpa using hfour 1
  have h2 : s.sourceTet₂.verts.Nodup := by simpa using hfour 2
  have h3 : s.sourceTet₃.verts.Nodup := by simpa using hfour 3
  have hrestN : ∀ τ ∈ rest, τ.verts.Nodup := by
    intro τ hτ
    exact hcore.1 τ (by simp [hτ])
  have hrestP : rest.Pairwise (fun τ σ => ¬ SameTetVertices τ σ) := by
    exact (List.pairwise_cons.mp hcore.2.1).2
  have hcenterSource (τ : Tet) (hτ : τ ∈ s.sourceTets) :
      s.e ∈ τ.verts := by
    simp [Move41Site.sourceTets] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;>
      simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
        Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]
  have hcross : ∀ τ ∈ s.sourceTets, ∀ ρ ∈ rest,
      ¬ SameTetVertices τ ρ := by
    intro τ hτ ρ hρ hsame
    exact hfresh ρ hρ ((hsame s.e).1 (hcenterSource τ hτ))
  constructor
  · intro τ hτ
    simp only [Move41Site.headStellar, List.mem_cons] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | hτ
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact hrestN τ hτ
  · have hp : (s.sourceTet₀ :: s.sourceTet₁ :: s.sourceTet₂ ::
        s.sourceTet₃ :: ([] : List Tet)).Pairwise
        (fun τ σ => ¬ SameTetVertices τ σ) := by
      simpa [Move41Site.sourceTets] using s.sourceTets_pairwise_of_distinct
    have hp0 := (List.pairwise_cons.mp hp).1
    have hp1 := (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).1
    have hp2 :=
      (List.pairwise_cons.mp
        (List.pairwise_cons.mp (List.pairwise_cons.mp hp).2).2).1
    simp only [Move41Site.headStellar, List.pairwise_cons]
    refine ⟨?_, ?_, ?_, ?_, hrestP⟩
    · intro ρ hρ
      simp only [List.mem_cons] at hρ
      rcases hρ with rfl | rfl | rfl | hρ
      · exact hp0 _ (by simp)
      · exact hp0 _ (by simp)
      · exact hp0 _ (by simp)
      · exact hcross s.sourceTet₀ (by simp [Move41Site.sourceTets]) ρ hρ
    · intro ρ hρ
      simp only [List.mem_cons] at hρ
      rcases hρ with rfl | rfl | hρ
      · exact hp1 _ (by simp)
      · exact hp1 _ (by simp)
      · exact hcross s.sourceTet₁ (by simp [Move41Site.sourceTets]) ρ hρ
    · intro ρ hρ
      simp only [List.mem_cons] at hρ
      rcases hρ with rfl | hρ
      · exact hp2 _ (by simp)
      · exact hcross s.sourceTet₂ (by simp [Move41Site.sourceTets]) ρ hρ
    · intro ρ hρ
      exact hcross s.sourceTet₃ (by simp [Move41Site.sourceTets]) ρ hρ

end Poincare
