import Poincare.Move32SurvivorClassification

namespace Poincare

/-- The combinatorial data of a genuine `4 → 1` bistellar move.  The vertex
`e` is the center of the four source tetrahedra. -/
structure Move41Site where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  distinct : [a, b, c, d, e].Nodup

def Move41Site.sourceTet₀ (s : Move41Site) : Tet := ⟨s.a, s.b, s.c, s.e⟩
def Move41Site.sourceTet₁ (s : Move41Site) : Tet := ⟨s.a, s.b, s.d, s.e⟩
def Move41Site.sourceTet₂ (s : Move41Site) : Tet := ⟨s.a, s.c, s.d, s.e⟩
def Move41Site.sourceTet₃ (s : Move41Site) : Tet := ⟨s.b, s.c, s.d, s.e⟩
def Move41Site.targetTet (s : Move41Site) : Tet := ⟨s.a, s.b, s.c, s.d⟩

def Move41Site.sourceTets (s : Move41Site) : List Tet :=
  [s.sourceTet₀, s.sourceTet₁, s.sourceTet₂, s.sourceTet₃]

/-- Exact local bistellar data.  `closedCore` supplies every face-incidence
condition, while the remaining fields identify the saturated center star and
exclude the target tetrahedron. -/
structure Move41Site.LegalIn (s : Move41Site) (K : Triangulation) : Prop where
  closedCore : ClosedTriangulationCore K
  sourceOccursExactlyOnce :
    ∀ source ∈ s.sourceTets,
      (K.tets.filter (fun τ => sameTetVerticesBool τ source)).length = 1
  sourcePairwiseDistinct :
    s.sourceTets.Pairwise (fun τ σ => ¬ SameTetVertices τ σ)
  centerSaturated :
    ∀ τ ∈ K.tets, s.e ∈ τ.verts →
      ∃ source ∈ s.sourceTets, SameTetVertices τ source
  targetAbsent :
    ∀ τ ∈ K.tets, ¬ SameTetVertices τ s.targetTet

/-- In a legal `4 → 1` move, the tetrahedra incident to the center are
exactly the four declared source tetrahedra, up to vertex ordering. -/
theorem Move41Site.mem_source_iff_of_center_mem
    {s : Move41Site} {K : Triangulation} (h : s.LegalIn K) {τ : Tet}
    (hτ : τ ∈ K.tets) :
    s.e ∈ τ.verts ↔ ∃ source ∈ s.sourceTets, SameTetVertices τ source := by
  constructor
  · exact h.centerSaturated τ hτ
  · rintro ⟨source, hsource, hsame⟩
    have heSource : s.e ∈ source.verts := by
      simp [Move41Site.sourceTets] at hsource
      rcases hsource with rfl | rfl | rfl | rfl <;>
        simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
          Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]
    exact (hsame s.e).2 heSource

/-- The tetrahedra outside the `4 → 1` region, obtained by erasing exactly
one representative of each of the four source vertex sets. -/
def Move41Site.unchangedTets (s : Move41Site) (K : Triangulation) : List Tet :=
  eraseFirstSameTet s.sourceTet₃
    (eraseFirstSameTet s.sourceTet₂
      (eraseFirstSameTet s.sourceTet₁
        (eraseFirstSameTet s.sourceTet₀ K.tets)))

/-- Exact `4 → 1` replacement: erase the four source tetrahedra and insert
the opposite tetrahedron. -/
def Move41Site.replace (s : Move41Site) (K : Triangulation) : Triangulation :=
  { tets := s.targetTet :: s.unchangedTets K }

/-- In the result of a legal `4 → 1` replacement, the explicitly inserted
tetrahedron is the unique representative of its vertex set. -/
theorem Move41Site.same_target_iff_eq_of_mem_replace
    {s : Move41Site} {K : Triangulation} (h : s.LegalIn K) {τ : Tet}
    (hτ : τ ∈ (s.replace K).tets) :
    SameTetVertices τ s.targetTet ↔ τ = s.targetTet := by
  constructor
  · intro hsame
    simp only [Move41Site.replace, List.mem_cons] at hτ
    rcases hτ with rfl | hunchanged
    · rfl
    · have horiginal : τ ∈ K.tets := by
        exact mem_of_mem_eraseFirstSameTet
          (mem_of_mem_eraseFirstSameTet
            (mem_of_mem_eraseFirstSameTet
              (mem_of_mem_eraseFirstSameTet hunchanged)))
      exact (h.targetAbsent τ horiginal hsame).elim
  · rintro rfl
    exact fun _ => Iff.rfl

/-- A genuine `4 → 1` replacement removes its center from the vertex
support. -/
theorem Move41Site.center_not_mem_vertexSupport_replace
    {s : Move41Site} {K : Triangulation} (h : s.LegalIn K) :
    s.e ∉ vertexSupport (s.replace K) := by
  rw [mem_vertexSupport_iff]
  intro he
  simp only [allVerts, List.mem_flatMap] at he
  rcases he with ⟨τ, hτ, heτ⟩
  simp only [Move41Site.replace, List.mem_cons] at hτ
  rcases hτ with rfl | hunchanged
  · simp [Move41Site.targetTet, Tet.verts] at heτ
    have hd := s.distinct
    simp at hd
    aesop
  · have hsource :=
      (Move41Site.mem_source_iff_of_center_mem h
        (mem_of_mem_eraseFirstSameTet
          (mem_of_mem_eraseFirstSameTet
            (mem_of_mem_eraseFirstSameTet
              (mem_of_mem_eraseFirstSameTet hunchanged))))).1 heτ
    rcases hsource with ⟨source, hsource, hsame⟩
    have sourceExists : ∃ ρ ∈ K.tets, SameTetVertices ρ source := by
      have hlength := h.sourceOccursExactlyOnce source hsource
      have hne : K.tets.filter (fun σ => sameTetVerticesBool σ source) ≠ [] := by
        intro hempty
        simp [hempty] at hlength
      rcases List.exists_mem_of_ne_nil _ hne with ⟨ρ, hρ⟩
      exact ⟨ρ, by simpa [sameTetVerticesBool_eq_true_iff] using hρ⟩
    have sourceUnique := h.closedCore.existsUnique_sameTetVertices sourceExists
    have hnK : K.tets.Nodup := by
      exact h.closedCore.2.1.imp (fun hnot heq =>
        hnot (by subst heq; exact sameTetVertices_refl _))
    have hp := h.sourcePairwiseDistinct
    simp [Move41Site.sourceTets] at hp
    simp [Move41Site.sourceTets] at hsource
    rcases hsource with rfl | rfl | rfl | rfl
    · exact (not_same_of_mem_eraseFirstSameTet_of_unique hnK sourceUnique
        (mem_of_mem_eraseFirstSameTet
          (mem_of_mem_eraseFirstSameTet
            (mem_of_mem_eraseFirstSameTet hunchanged)))) hsame
    · have hu := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
          sourceUnique (fun hsame => hp.1.1 (sameTetVertices_symm hsame))
      have hafter := mem_of_mem_eraseFirstSameTet
        (mem_of_mem_eraseFirstSameTet hunchanged)
      exact (not_same_of_mem_eraseFirstSameTet_of_unique
        (hnK.sublist (eraseFirstSameTet_sublist _ _)) hu hafter) hsame
    · have hu := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
          sourceUnique (fun hsame => hp.1.2.1 (sameTetVertices_symm hsame))
      have hu' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
          hu (fun hsame => hp.2.1.1 (sameTetVertices_symm hsame))
      have hafter := mem_of_mem_eraseFirstSameTet hunchanged
      exact (not_same_of_mem_eraseFirstSameTet_of_unique
        ((hnK.sublist (eraseFirstSameTet_sublist _ _)).sublist
          (eraseFirstSameTet_sublist _ _)) hu' hafter) hsame
    · have hu := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
          sourceUnique (fun hsame => hp.1.2.2 (sameTetVertices_symm hsame))
      have hu' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
          hu (fun hsame => hp.2.1.2 (sameTetVertices_symm hsame))
      have hu'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
          hu' (fun hsame => hp.2.2 (sameTetVertices_symm hsame))
      exact (not_same_of_mem_eraseFirstSameTet_of_unique
        (((hnK.sublist (eraseFirstSameTet_sublist _ _)).sublist
          (eraseFirstSameTet_sublist _ _)).sublist
            (eraseFirstSameTet_sublist _ _)) hu'' hunchanged) hsame

/-- Away from the removed center, a genuine `4 → 1` replacement preserves
vertex-support membership. -/
theorem Move41Site.mem_vertexSupport_replace_iff_of_ne_center
    {s : Move41Site} {K : Triangulation} (h : s.LegalIn K) {v : Nat}
    (hve : v ≠ s.e) :
    v ∈ vertexSupport (s.replace K) ↔ v ∈ vertexSupport K := by
  rw [mem_vertexSupport_iff, mem_vertexSupport_iff]
  simp only [allVerts, List.mem_flatMap]
  have sourceExists (source : Tet) (hsource : source ∈ s.sourceTets) :
      ∃ ρ ∈ K.tets, SameTetVertices ρ source := by
    have hlength := h.sourceOccursExactlyOnce source hsource
    have hne : K.tets.filter
        (fun σ => sameTetVerticesBool σ source) ≠ [] := by
      intro hempty
      simp [hempty] at hlength
    rcases List.exists_mem_of_ne_nil _ hne with ⟨ρ, hρ⟩
    have hρ' : ρ ∈ K.tets ∧ SameTetVertices ρ source := by
      simpa [sameTetVerticesBool_eq_true_iff] using hρ
    exact ⟨ρ, hρ'.1, hρ'.2⟩
  constructor
  · rintro ⟨τ, hτ, hvτ⟩
    simp only [Move41Site.replace, List.mem_cons] at hτ
    rcases hτ with rfl | hunchanged
    · have hvTarget :
          v = s.a ∨ v = s.b ∨ v = s.c ∨ v = s.d := by
        simpa [Move41Site.targetTet, Tet.verts] using hvτ
      rcases hvTarget with rfl | rfl | rfl | rfl
      · rcases sourceExists s.sourceTet₀ (by simp [Move41Site.sourceTets]) with
          ⟨ρ, hρ, hsame⟩
        exact ⟨ρ, hρ, (hsame _).2 (by simp [Move41Site.sourceTet₀, Tet.verts])⟩
      · rcases sourceExists s.sourceTet₀ (by simp [Move41Site.sourceTets]) with
          ⟨ρ, hρ, hsame⟩
        exact ⟨ρ, hρ, (hsame _).2 (by simp [Move41Site.sourceTet₀, Tet.verts])⟩
      · rcases sourceExists s.sourceTet₀ (by simp [Move41Site.sourceTets]) with
          ⟨ρ, hρ, hsame⟩
        exact ⟨ρ, hρ, (hsame _).2 (by simp [Move41Site.sourceTet₀, Tet.verts])⟩
      · rcases sourceExists s.sourceTet₁ (by simp [Move41Site.sourceTets]) with
          ⟨ρ, hρ, hsame⟩
        exact ⟨ρ, hρ, (hsame _).2 (by simp [Move41Site.sourceTet₁, Tet.verts])⟩
    · exact ⟨τ, mem_of_mem_eraseFirstSameTet
          (mem_of_mem_eraseFirstSameTet
            (mem_of_mem_eraseFirstSameTet
              (mem_of_mem_eraseFirstSameTet hunchanged))), hvτ⟩
  · rintro ⟨τ, hτ, hvτ⟩
    by_cases heτ : s.e ∈ τ.verts
    · rcases (Move41Site.mem_source_iff_of_center_mem h hτ).1 heτ with
        ⟨source, hsource, hsame⟩
      have hvSource : v ∈ source.verts := (hsame v).1 hvτ
      have hvTarget : v ∈ s.targetTet.verts := by
        simp [Move41Site.sourceTets] at hsource
        rcases hsource with rfl | rfl | rfl | rfl <;>
          simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
            Move41Site.sourceTet₂, Move41Site.sourceTet₃,
            Move41Site.targetTet, Tet.verts] at hvSource ⊢ <;> aesop
      exact ⟨s.targetTet, by simp [Move41Site.replace], hvTarget⟩
    · have hnotSource : ∀ source ∈ s.sourceTets,
          ¬ SameTetVertices τ source := by
        intro source hsource hsame
        apply heτ
        apply (hsame s.e).2
        simp [Move41Site.sourceTets] at hsource
        rcases hsource with rfl | rfl | rfl | rfl <;>
          simp [Move41Site.sourceTet₀, Move41Site.sourceTet₁,
            Move41Site.sourceTet₂, Move41Site.sourceTet₃, Tet.verts]
      have hunchanged : τ ∈ s.unchangedTets K := by
        apply mem_eraseFirstSameTet_of_mem_of_not_same
        · apply mem_eraseFirstSameTet_of_mem_of_not_same
          · apply mem_eraseFirstSameTet_of_mem_of_not_same
            · exact mem_eraseFirstSameTet_of_mem_of_not_same hτ
                (hnotSource s.sourceTet₀ (by simp [Move41Site.sourceTets]))
            · exact hnotSource s.sourceTet₁ (by simp [Move41Site.sourceTets])
          · exact hnotSource s.sourceTet₂ (by simp [Move41Site.sourceTets])
        · exact hnotSource s.sourceTet₃ (by simp [Move41Site.sourceTets])
      exact ⟨τ, by simp [Move41Site.replace, hunchanged], hvτ⟩

end Poincare
