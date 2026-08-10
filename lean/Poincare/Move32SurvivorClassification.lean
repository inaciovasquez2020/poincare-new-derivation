import Poincare.Move32CombinatorialFoundation
import Poincare.Move23UnchangedOverlap

namespace Poincare

theorem sameTetVertices_refl (tau : Tet) : SameTetVertices tau tau :=
  fun _ => Iff.rfl

theorem sameTetVertices_symm {tau rho : Tet} :
    SameTetVertices tau rho → SameTetVertices rho tau := by
  intro h v
  exact (h v).symm

theorem sameTetVertices_trans {tau rho sigma : Tet} :
    SameTetVertices tau rho → SameTetVertices rho sigma → SameTetVertices tau sigma := by
  intro htr hrs v
  exact (htr v).trans (hrs v)

theorem ClosedTriangulationCore.existsUnique_sameTetVertices
    {K : Triangulation} (hcore : ClosedTriangulationCore K) {target : Tet}
    (hex : ∃ tau ∈ K.tets, SameTetVertices tau target) :
    ∃! tau : Tet, tau ∈ K.tets ∧ SameTetVertices tau target := by
  rcases hex with ⟨tau, htau, hsame⟩
  refine ⟨tau, ⟨htau, hsame⟩, ?_⟩
  intro rho hrho
  exact hcore.eq_of_mem_of_sameTetVertices hrho.1 htau
    (sameTetVertices_trans hrho.2 (sameTetVertices_symm hsame))

theorem existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same
    {remove keep : Tet} {tets : List Tet}
    (hu : ∃! rho : Tet, rho ∈ tets ∧ SameTetVertices rho keep)
    (hne : ¬ SameTetVertices keep remove) :
    ∃! rho : Tet,
      rho ∈ eraseFirstSameTet remove tets ∧ SameTetVertices rho keep := by
  rcases hu with ⟨rho, hrho, huniq⟩
  have hn : ¬ SameTetVertices rho remove := by
    intro hremove
    exact hne (sameTetVertices_trans (sameTetVertices_symm hrho.2) hremove)
  refine ⟨rho, ⟨mem_eraseFirstSameTet_of_mem_of_not_same hrho.1 hn, hrho.2⟩, ?_⟩
  intro x hx
  exact huniq x ⟨mem_of_mem_eraseFirstSameTet hx.1, hx.2⟩

theorem Move32Site.targetTet₀_not_same_targetTet₁ (s : Move32Site)
    (hfive : [s.a, s.b, s.c, s.d, s.e].Nodup) :
    ¬ SameTetVertices s.targetTet₀ s.targetTet₁ := by
  intro h
  have hb : s.b ∈ s.targetTet₀.verts := by simp [Move32Site.targetTet₀, Tet.verts]
  have := (h s.b).1 hb
  simp [Move32Site.targetTet₁, Tet.verts] at this
  simp at hfive
  aesop

theorem Move32Site.targetTet₀_not_same_targetTet₂ (s : Move32Site)
    (hfive : [s.a, s.b, s.c, s.d, s.e].Nodup) :
    ¬ SameTetVertices s.targetTet₀ s.targetTet₂ := by
  intro h
  have ha : s.a ∈ s.targetTet₀.verts := by simp [Move32Site.targetTet₀, Tet.verts]
  have := (h s.a).1 ha
  simp [Move32Site.targetTet₂, Tet.verts] at this
  simp at hfive
  aesop

theorem Move32Site.targetTet₁_not_same_targetTet₂ (s : Move32Site)
    (hfive : [s.a, s.b, s.c, s.d, s.e].Nodup) :
    ¬ SameTetVertices s.targetTet₁ s.targetTet₂ := by
  intro h
  have ha : s.a ∈ s.targetTet₁.verts := by simp [Move32Site.targetTet₁, Tet.verts]
  have := (h s.a).1 ha
  simp [Move32Site.targetTet₂, Tet.verts] at this
  simp at hfive
  aesop

theorem ClosedTriangulationCore.move32Site_survivor
    {K : Triangulation} (hcore : ClosedTriangulationCore K) (s : Move32Site)
    (hlegal : s.LegalIn K) {tau : Tet} (htau : tau ∈ s.unchangedTets K) :
    tau ∈ K.tets ∧ tau ∈ (s.replace K).tets ∧
    ¬ SameTetVertices tau s.targetTet₀ ∧
    ¬ SameTetVertices tau s.targetTet₁ ∧
    ¬ SameTetVertices tau s.targetTet₂ := by
  have hfive := hcore.move32Site_distinct s hlegal.1
  rcases hlegal.1 with ⟨h0, h1, h2⟩
  have hu0 := hcore.existsUnique_sameTetVertices h0
  have hu1 := hcore.existsUnique_sameTetVertices h1
  have hu2 := hcore.existsUnique_sameTetVertices h2
  have hnK : K.tets.Nodup := hcore.2.1.imp (by
    intro x y hxy heq
    subst y
    exact hxy (sameTetVertices_refl x))
  have hn0 : (eraseFirstSameTet s.targetTet₀ K.tets).Nodup :=
    hnK.sublist (eraseFirstSameTet_sublist _ _)
  have hn1 : (eraseFirstSameTet s.targetTet₁
      (eraseFirstSameTet s.targetTet₀ K.tets)).Nodup :=
    hn0.sublist (eraseFirstSameTet_sublist _ _)
  have hm1 : tau ∈ eraseFirstSameTet s.targetTet₁
      (eraseFirstSameTet s.targetTet₀ K.tets) :=
    mem_of_mem_eraseFirstSameTet htau
  have hm0 : tau ∈ eraseFirstSameTet s.targetTet₀ K.tets :=
    mem_of_mem_eraseFirstSameTet hm1
  have hnot0 := not_same_of_mem_eraseFirstSameTet_of_unique hnK hu0 hm0
  have hu1' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu1
    (fun h => s.targetTet₀_not_same_targetTet₁ hfive (sameTetVertices_symm h))
  have hnot1 := not_same_of_mem_eraseFirstSameTet_of_unique hn0 hu1' hm1
  have hu2' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2
    (fun h => s.targetTet₀_not_same_targetTet₂ hfive (sameTetVertices_symm h))
  have hu2'' := existsUnique_sameTetVertices_eraseFirstSameTet_of_not_same hu2'
    (fun h => s.targetTet₁_not_same_targetTet₂ hfive (sameTetVertices_symm h))
  have hnot2 := not_same_of_mem_eraseFirstSameTet_of_unique hn1 hu2'' htau
  exact ⟨s.mem_original_of_mem_unchanged htau, by
      rw [s.replace_tets_eq K]
      simp [htau], hnot0, hnot1, hnot2⟩

theorem eq_one_of_three_of_mem_of_length_eq_three
    {α : Type} {l : List α} {x x0 x1 x2 : α}
    (hlen : l.length = 3) (h0 : x0 ∈ l) (h1 : x1 ∈ l) (h2 : x2 ∈ l)
    (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) (hx : x ∈ l) :
    x = x0 ∨ x = x1 ∨ x = x2 := by
  obtain ⟨u, v, w, rfl⟩ := List.length_eq_three.mp hlen
  simp only [List.mem_cons] at h0 h1 h2 hx
  aesop

theorem ClosedTriangulationCore.move32Site_same_target_of_contains_sharedEdge
    {K : Triangulation} (hcore : ClosedTriangulationCore K) (s : Move32Site)
    (hlegal : s.LegalIn K) {tau : Tet} (htau : tau ∈ K.tets)
    (hd : s.d ∈ tau.verts) (he : s.e ∈ tau.verts) :
    SameTetVertices tau s.targetTet₀ ∨ SameTetVertices tau s.targetTet₁ ∨
      SameTetVertices tau s.targetTet₂ := by
  rcases hlegal.1 with ⟨⟨t0, ht0, hs0⟩, ⟨t1, ht1, hs1⟩, ⟨t2, ht2, hs2⟩⟩
  have hfive := hcore.move32Site_distinct s
    ⟨⟨t0, ht0, hs0⟩, ⟨t1, ht1, hs1⟩, ⟨t2, ht2, hs2⟩⟩
  let edgeTets := K.tets.filter (fun rho => s.d ∈ rho.verts ∧ s.e ∈ rho.verts)
  have memEdge {rho : Tet} (hr : rho ∈ K.tets) (hs : SameTetVertices rho s.targetTet₀ ∨
      SameTetVertices rho s.targetTet₁ ∨ SameTetVertices rho s.targetTet₂) : rho ∈ edgeTets := by
    simp only [edgeTets, List.mem_filter, decide_eq_true_eq]
    refine ⟨hr, ?_⟩
    rcases hs with hs | hs | hs
    all_goals constructor <;> apply (hs _).2 <;>
      simp [Move32Site.targetTet₀, Move32Site.targetTet₁, Move32Site.targetTet₂, Tet.verts]
  have hm0 : t0 ∈ edgeTets := memEdge ht0 (Or.inl hs0)
  have hm1 : t1 ∈ edgeTets := memEdge ht1 (Or.inr (Or.inl hs1))
  have hm2 : t2 ∈ edgeTets := memEdge ht2 (Or.inr (Or.inr hs2))
  have h01 : t0 ≠ t1 := by
    intro h; subst t1
    exact s.targetTet₀_not_same_targetTet₁ hfive
      (sameTetVertices_trans (sameTetVertices_symm hs0) hs1)
  have h02 : t0 ≠ t2 := by
    intro h; subst t2
    exact s.targetTet₀_not_same_targetTet₂ hfive
      (sameTetVertices_trans (sameTetVertices_symm hs0) hs2)
  have h12 : t1 ≠ t2 := by
    intro h; subst t2
    exact s.targetTet₁_not_same_targetTet₂ hfive
      (sameTetVertices_trans (sameTetVertices_symm hs1) hs2)
  have hmt : tau ∈ edgeTets := by simp [edgeTets, htau, hd, he]
  rcases eq_one_of_three_of_mem_of_length_eq_three hlegal.2.1 hm0 hm1 hm2 h01 h02 h12 hmt with
    rfl | rfl | rfl
  · exact Or.inl hs0
  · exact Or.inr (Or.inl hs1)
  · exact Or.inr (Or.inr hs2)

theorem ClosedTriangulationCore.move32Site_unchangedTet_not_contains_sharedEdge
    {K : Triangulation} (hcore : ClosedTriangulationCore K) (s : Move32Site)
    (hlegal : s.LegalIn K) {tau : Tet} (htau : tau ∈ s.unchangedTets K) :
    ¬ (s.d ∈ tau.verts ∧ s.e ∈ tau.verts) := by
  intro h
  have hs := hcore.move32Site_survivor s hlegal htau
  exact (hcore.move32Site_same_target_of_contains_sharedEdge s hlegal hs.1 h.1 h.2).elim
    hs.2.2.1 (fun hrest => hrest.elim hs.2.2.2.1 hs.2.2.2.2)

theorem ClosedTriangulationCore.move32Site_unchangedTet_not_contains_sourceFace
    {K : Triangulation} (hcore : ClosedTriangulationCore K) (s : Move32Site)
    (hlegal : s.LegalIn K) {tau : Tet} (htau : tau ∈ s.unchangedTets K) :
    ¬ (s.a ∈ tau.verts ∧ s.b ∈ tau.verts ∧ s.c ∈ tau.verts) :=
  hlegal.2.2 tau (hcore.move32Site_survivor s hlegal htau).1

theorem ClosedTriangulationCore.move32Site_ofMove23Site_legal_replace
    {K : Triangulation} (hcore : ClosedTriangulationCore K) (m : Move23Site)
    (hlegal : m.LegalIn K) :
    (Move32Site.ofMove23Site m).LegalIn (m.replace K) := by
  have hfive := hcore.move23Site_distinct_independent (s := m) hlegal.1 hlegal.2.2
  refine ⟨?_, ?_, ?_⟩
  · rcases m.newTets_mem_replace K with ⟨h0, h1, h2⟩
    exact ⟨⟨m.newTet₀, h0, sameTetVertices_refl _⟩,
      ⟨m.newTet₁, h1, sameTetVertices_refl _⟩,
      ⟨m.newTet₂, h2, sameTetVertices_refl _⟩⟩
  · change ((m.replace K).tets.filter
      (fun tau => m.d ∈ tau.verts ∧ m.e ∈ tau.verts)).length = 3
    rw [m.replace_tets_eq K]
    have htail : (m.unchangedTets K).filter
        (fun tau => m.d ∈ tau.verts ∧ m.e ∈ tau.verts) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro tau htau
      simpa using hlegal.2.2 tau
        (hcore.move23Site_mem_unchangedTets m hlegal htau).1
    rw [List.filter_cons, List.filter_cons, List.filter_cons, htail]
    simp [Move23Site.newTet₀, Move23Site.newTet₁, Move23Site.newTet₂, Tet.verts]
  · change ∀ tau ∈ (m.replace K).tets,
      ¬ (m.a ∈ tau.verts ∧ m.b ∈ tau.verts ∧ m.c ∈ tau.verts)
    intro tau htau
    rw [m.replace_tets_eq K] at htau
    simp only [List.mem_cons] at htau
    rcases htau with rfl | rfl | rfl | htau
    · simp [Move23Site.newTet₀, Tet.verts]
      simp at hfive
      aesop
    · simp [Move23Site.newTet₁, Tet.verts]
      simp at hfive
      aesop
    · simp [Move23Site.newTet₂, Tet.verts]
      simp at hfive
      aesop
    · simpa [Move32Site.ofMove23Site] using
        hcore.move23Site_unchangedTet_not_contains_sharedFace m hlegal htau

end Poincare
