import Poincare.Move32SurvivorClassification
import Poincare.TetrahedronFaceClassification
import Poincare.Move23FaceIncidenceTable

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

/-- A genuine `4 → 1` replacement decreases the number of supported
vertices by exactly one. -/
theorem Move41Site.vertexSupport_toFinset_card_replace_add_one_eq
    {s : Move41Site} {K : Triangulation} (h : s.LegalIn K) :
    (vertexSupport (s.replace K)).toFinset.card + 1 =
      (vertexSupport K).toFinset.card := by
  have heSupport : s.e ∈ vertexSupport K := by
    rw [mem_vertexSupport_iff]
    simp only [allVerts, List.mem_flatMap]
    have hlength := h.sourceOccursExactlyOnce s.sourceTet₀ (by
      simp [Move41Site.sourceTets])
    have hne : K.tets.filter
        (fun τ => sameTetVerticesBool τ s.sourceTet₀) ≠ [] := by
      intro hempty
      simp [hempty] at hlength
    rcases List.exists_mem_of_ne_nil _ hne with ⟨τ, hτ⟩
    have hτ' : τ ∈ K.tets ∧ SameTetVertices τ s.sourceTet₀ := by
      simpa [sameTetVerticesBool_eq_true_iff] using hτ
    exact ⟨τ, hτ'.1, (hτ'.2 s.e).2 (by
      simp [Move41Site.sourceTet₀, Tet.verts])⟩
  have hsupport : (vertexSupport (s.replace K)).toFinset =
      (vertexSupport K).toFinset.erase s.e := by
    ext v
    by_cases hve : v = s.e
    · subst v
      simp [Move41Site.center_not_mem_vertexSupport_replace h]
    · simp [hve, Move41Site.mem_vertexSupport_replace_iff_of_ne_center h hve]
  have heSupport' : s.e ∈ (vertexSupport K).toFinset := by
    simpa using heSupport
  rw [hsupport, Finset.card_erase_add_one heSupport']

/-- A genuine `4 → 1` replacement preserves tetrahedron nondegeneracy and
vertex-set uniqueness.  Exact triangular-face incidence is the remaining
closed-core obligation. -/
theorem ClosedTriangulationCore.move41Site_replace_simple
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    (∀ τ ∈ (s.replace K).tets, τ.verts.Nodup) ∧
      (s.replace K).tets.Pairwise
        (fun τ σ => ¬ SameTetVertices τ σ) := by
  have htargetNodup : s.targetTet.verts.Nodup := by
    have hd := s.distinct
    simp [Move41Site.targetTet, Tet.verts] at ⊢
    simp at hd
    aesop
  have hsub : List.Sublist (s.unchangedTets K) K.tets := by
    exact (eraseFirstSameTet_sublist s.sourceTet₃ _).trans
      ((eraseFirstSameTet_sublist s.sourceTet₂ _).trans
        ((eraseFirstSameTet_sublist s.sourceTet₁ _).trans
          (eraseFirstSameTet_sublist s.sourceTet₀ _)))
  have hunchangedNodup :
      ∀ τ ∈ s.unchangedTets K, τ.verts.Nodup := by
    intro τ hτ
    exact hcore.1 τ (hsub.subset hτ)
  have hunchangedPairwise :
      (s.unchangedTets K).Pairwise
        (fun τ σ => ¬ SameTetVertices τ σ) :=
    hcore.2.1.sublist hsub
  have htargetUnchanged : ∀ τ ∈ s.unchangedTets K,
      ¬ SameTetVertices s.targetTet τ := by
    intro τ hτ hsame
    exact hlegal.targetAbsent τ (hsub.subset hτ)
      (sameTetVertices_symm hsame)
  constructor
  · intro τ hτ
    simp only [Move41Site.replace, List.mem_cons] at hτ
    rcases hτ with rfl | hτ
    · exact htargetNodup
    · exact hunchangedNodup τ hτ
  · simp only [Move41Site.replace, List.pairwise_cons]
    exact ⟨htargetUnchanged, hunchangedPairwise⟩

section Move41ClosedCore

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-- A legal genuine `4 → 1` replacement preserves exact two-fold
incidence of every represented nondegenerate triangular face. -/
theorem ClosedTriangulationCore.move41Site_replace_closedCore
    {K : Triangulation} (hcore : ClosedTriangulationCore K)
    (s : Move41Site) (hlegal : s.LegalIn K) :
    ClosedTriangulationCore (s.replace K) := by
  refine ⟨(hcore.move41Site_replace_simple s hlegal).1,
    (hcore.move41Site_replace_simple s hlegal).2, ?_⟩
  intro x y z hxyz hrepresented
  let p : Tet → Prop := fun τ =>
    x ∈ τ.verts ∧ y ∈ τ.verts ∧ z ∈ τ.verts
  have hinvariant : ∀ τ σ, SameTetVertices τ σ → (p τ ↔ p σ) := by
    intro τ σ hsame
    simp only [p]
    constructor <;> intro h
    · exact ⟨(hsame x).1 h.1, (hsame y).1 h.2.1, (hsame z).1 h.2.2⟩
    · exact ⟨(hsame x).2 h.1, (hsame y).2 h.2.1, (hsame z).2 h.2.2⟩
  have hfilter (L : List Tet) :
      (L.filter p).length =
        (L.filter fun τ => τ.ContainsTriple x y z).length := by
    congr 2
    funext τ
    simp [p, Tet.ContainsTriple]
  have sourceUnique (source : Tet) (hsource : source ∈ s.sourceTets) :
      ∃! τ, τ ∈ K.tets ∧ SameTetVertices τ source := by
    have hlen := hlegal.sourceOccursExactlyOnce source hsource
    have hex : ∃ τ ∈ K.tets, SameTetVertices τ source := by
      have hne : K.tets.filter
          (fun τ => sameTetVerticesBool τ source) ≠ [] := by
        intro hempty
        simp [hempty] at hlen
      rcases List.exists_mem_of_ne_nil _ hne with ⟨τ, hτ⟩
      exact ⟨τ, by simpa [sameTetVerticesBool_eq_true_iff] using hτ⟩
    exact hcore.existsUnique_sameTetVertices hex
  have hp := hlegal.sourcePairwiseDistinct
  simp [Move41Site.sourceTets] at hp
  have hu0 := sourceUnique s.sourceTet₀ (by simp [Move41Site.sourceTets])
  have hu1 := sourceUnique s.sourceTet₁ (by simp [Move41Site.sourceTets])
  have hu2 := sourceUnique s.sourceTet₂ (by simp [Move41Site.sourceTets])
  have hu3 := sourceUnique s.sourceTet₃ (by simp [Move41Site.sourceTets])
  have hu1' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu1
    (fun h => hp.1.1 (sameTetVertices_symm h))
  have hu2' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2
    (fun h => hp.1.2.1 (sameTetVertices_symm h))
  have hu2'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2'
    (fun h => hp.2.1.1 (sameTetVertices_symm h))
  have hu3' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu3
    (fun h => hp.1.2.2 (sameTetVertices_symm h))
  have hu3'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu3'
    (fun h => hp.2.1.2 (sameTetVertices_symm h))
  have hu3''' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu3''
    (fun h => hp.2.2 (sameTetVertices_symm h))
  have eraseStep (source : Tet) (L : List Tet)
      (hu : ∃! τ, τ ∈ L ∧ SameTetVertices τ source) :
      ((eraseFirstSameTet source L).filter p).length +
          (if p source then 1 else 0) = (L.filter p).length := by
    by_cases hs : p source
    · simpa [hs] using eraseFirstSameTet_filter_length_add_one_eq
        p source L hinvariant
        ⟨hu.choose, hu.choose_spec.1.1, hu.choose_spec.1.2⟩ hs
    · simpa [hs] using eraseFirstSameTet_filter_length_eq_of_not
        p source L hinvariant hs
  have e0 := eraseStep s.sourceTet₀ K.tets hu0
  have e1 := eraseStep s.sourceTet₁
    (eraseFirstSameTet s.sourceTet₀ K.tets) hu1'
  have e2 := eraseStep s.sourceTet₂
    (eraseFirstSameTet s.sourceTet₁
      (eraseFirstSameTet s.sourceTet₀ K.tets)) hu2''
  have e3 := eraseStep s.sourceTet₃
    (eraseFirstSameTet s.sourceTet₂
      (eraseFirstSameTet s.sourceTet₁
        (eraseFirstSameTet s.sourceTet₀ K.tets))) hu3'''
  have hsplit :
      ((s.unchangedTets K).filter p).length +
          ([s.sourceTet₀, s.sourceTet₁, s.sourceTet₂, s.sourceTet₃].filter p).length =
        (K.tets.filter p).length := by
    by_cases h0 : p s.sourceTet₀ <;> by_cases h1 : p s.sourceTet₁ <;>
      by_cases h2 : p s.sourceTet₂ <;> by_cases h3 : p s.sourceTet₃ <;>
      simp [Move41Site.unchangedTets, h0, h1, h2, h3] at e0 e1 e2 e3 ⊢ <;>
      omega
  change ((s.replace K).tets.filter p).length = 2
  by_cases htarget : p s.targetTet
  · have hface := Tet.distinct_triple_face_cases s.targetTet x y z hxyz
      htarget.1 htarget.2.1 htarget.2.2
    have hlocal :
        ([s.sourceTet₀, s.sourceTet₁, s.sourceTet₂, s.sourceTet₃].filter p).length = 1 := by
      rw [hfilter]
      rcases hface with h | h | h | h <;>
        rw [filter_containsTriple_length_eq_of_sameTripleVertices _ h] <;>
        simp [Tet.ContainsTriple, Move41Site.sourceTet₀,
          Move41Site.sourceTet₁, Move41Site.sourceTet₂,
          Move41Site.sourceTet₃, Move41Site.targetTet, Tet.verts] <;>
        have hd := s.distinct <;> simp at hd <;> simp_all [eq_comm]
    have hK : (K.tets.filter p).length = 2 := by
      have hlen : 0 <
          ([s.sourceTet₀, s.sourceTet₁, s.sourceTet₂, s.sourceTet₃].filter p).length := by
        omega
      rcases List.length_pos_iff_exists_mem.mp hlen with ⟨τ, hτ⟩
      simp only [List.mem_filter] at hτ
      have hs : τ ∈ s.sourceTets := by
        simpa [Move41Site.sourceTets] using hτ.1
      rcases (sourceUnique τ hs) with ⟨ρ, hρ, -⟩
      exact hcore.2.2 x y z hxyz
        ⟨ρ, hρ.1, (hinvariant ρ τ hρ.2).2 (of_decide_eq_true hτ.2)⟩
    simp [Move41Site.replace, htarget]
    omega
  · rcases hrepresented with ⟨τ, hτ, hpτ⟩
    simp only [Move41Site.replace, List.mem_cons] at hτ
    rcases hτ with rfl | hτ
    · exact (htarget hpτ).elim
    · have horig : τ ∈ K.tets := mem_of_mem_eraseFirstSameTet
        (mem_of_mem_eraseFirstSameTet
          (mem_of_mem_eraseFirstSameTet
            (mem_of_mem_eraseFirstSameTet hτ)))
      have hK : (K.tets.filter p).length = 2 :=
        hcore.2.2 x y z hxyz ⟨τ, horig, hpτ⟩
      have hnotSource (source : Tet) (hs : source ∈ s.sourceTets) : ¬ p source := by
        intro hps
        have he : s.e = x ∨ s.e = y ∨ s.e = z := by
          simp [Move41Site.sourceTets] at hs
          rcases hs with rfl | rfl | rfl | rfl <;>
            simp [p, Move41Site.sourceTet₀, Move41Site.sourceTet₁,
              Move41Site.sourceTet₂, Move41Site.sourceTet₃,
              Move41Site.targetTet, Tet.verts] at hps htarget
          all_goals
            have hd := s.distinct
            simp at hd
            aesop
        have heτ : s.e ∈ τ.verts := he.elim
          (fun hx => hx.symm ▸ hpτ.1)
          (fun hyz => hyz.elim (fun hy => hy.symm ▸ hpτ.2.1)
            (fun hz => hz.symm ▸ hpτ.2.2))
        apply Move41Site.center_not_mem_vertexSupport_replace hlegal
        rw [mem_vertexSupport_iff]
        simp only [allVerts, List.mem_flatMap]
        exact ⟨τ, by simp [Move41Site.replace, hτ], heτ⟩
      have hlocal :
          ([s.sourceTet₀, s.sourceTet₁, s.sourceTet₂, s.sourceTet₃].filter p).length = 0 := by
        simp [hnotSource s.sourceTet₀ (by simp [Move41Site.sourceTets]),
          hnotSource s.sourceTet₁ (by simp [Move41Site.sourceTets]),
          hnotSource s.sourceTet₂ (by simp [Move41Site.sourceTets]),
          hnotSource s.sourceTet₃ (by simp [Move41Site.sourceTets])]
      simp [Move41Site.replace, htarget]
      omega

end Move41ClosedCore

end Poincare
