import Poincare.GlobalFanChordMove2332SecondStep
import Poincare.GlobalMove32SharedEdgeThreeTetSaturation
import Mathlib.Tactic

/-!
Read-only candidate for compilation in an isolated overlay.
Target repository HEAD: 03172442ae2d83ed0630c92b6aeb795269168e7a
No additional unproved declarations. This file is NOT compiled in the present environment.

The purpose is to discharge the 'second transverse outside the old face'
portion WITHOUT assuming second Move32Site.LegalIn. The remaining full
three-corner extraction and high-spoke composition are NOT asserted here.
-/
namespace Poincare

/-- The first legal `3→2` on `(m.a,m.b)` cannot recreate the old
`2→3` shared face `(m.a,m.b,m.c)`, provided `m.c` is not one
of the first `3→2` source-face vertices. -/
theorem Move23Site.old_sharedFace_absent_after_first_move32
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hsd : s.d = m.a) (hse : s.e = m.b)
    (hslegal : s.LegalIn (m.replace K)) :
    ∀ τ ∈ (s.replace (m.replace K)).tets,
      ¬ (m.a ∈ τ.verts ∧ m.b ∈ τ.verts ∧ m.c ∈ τ.verts) := by
  have hnotc : m.c ∉ [s.a,s.b,s.c] :=
    m.move32_candidate_sourceFace_not_contains_oldThird
      hcore hlegal s hsd hse hslegal.1
  have hm := m.distinct
  simp at hm
  intro τ hτ hface
  rw [s.replace_tets_eq] at hτ
  simp only [List.mem_cons] at hτ
  rcases hτ with rfl | rfl | hret
  · have hc : m.c ∈ s.sourceTet₀.verts := hface.2.2
    simp only [Move32Site.sourceTet₀, Tet.verts,
      List.mem_cons, List.mem_singleton, or_false] at hc
    simp only [List.mem_cons, List.mem_singleton, or_false] at hnotc
    rw [hsd] at hc
    aesop
  · have hc : m.c ∈ s.sourceTet₁.verts := hface.2.2
    simp only [Move32Site.sourceTet₁, Tet.verts,
      List.mem_cons, List.mem_singleton, or_false] at hc
    simp only [List.mem_cons, List.mem_singleton, or_false] at hnotc
    rw [hse] at hc
    aesop
  · exact m.replace_sharedFace_absent hcore hlegal τ
      (Move32Site.mem_original_of_mem_unchanged hret) hface

/-- A realized second site on `(m.a,m.c)` has no old third vertex `m.b`
in its source face, because its represented targets would recreate the
old shared face, absent after the first prefix. No second legality assumed. -/
theorem Move23Site.second_candidate_sourceFace_not_contains_oldThird
    {K : Triangulation} (m : Move23Site) (s t : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hsd : s.d = m.a) (hse : s.e = m.b)
    (hslegal : s.LegalIn (m.replace K))
    (htd : t.d = m.a) (hte : t.e = m.c)
    (htrealized : t.RealizedIn (s.replace (m.replace K))) :
    m.b ∉ [t.a,t.b,t.c] := by
  have hOld :=
    m.old_sharedFace_absent_after_first_move32 s hcore hlegal hsd hse hslegal
  obtain ⟨⟨τ0, hτ0, hs0⟩, ⟨τ1, hτ1, hs1⟩, ⟨τ2, hτ2, hs2⟩⟩ := htrealized
  have ha0 : m.a ∈ τ0.verts := by
    have h : t.d ∈ τ0.verts :=
      (hs0 t.d).2 (by simp [Move32Site.targetTet₀, Tet.verts])
    simpa [htd] using h
  have hc0 : m.c ∈ τ0.verts := by
    have h : t.e ∈ τ0.verts :=
      (hs0 t.e).2 (by simp [Move32Site.targetTet₀, Tet.verts])
    simpa [hte] using h
  have ha1 : m.a ∈ τ1.verts := by
    have h : t.d ∈ τ1.verts :=
      (hs1 t.d).2 (by simp [Move32Site.targetTet₁, Tet.verts])
    simpa [htd] using h
  have hc1 : m.c ∈ τ1.verts := by
    have h : t.e ∈ τ1.verts :=
      (hs1 t.e).2 (by simp [Move32Site.targetTet₁, Tet.verts])
    simpa [hte] using h
  intro hb
  simp only [List.mem_cons, List.mem_singleton, or_false] at hb
  rcases hb with h0 | h1 | h2
  · have hb0 : m.b ∈ τ0.verts := by
      have h : t.a ∈ τ0.verts :=
        (hs0 t.a).2 (by simp [Move32Site.targetTet₀, Tet.verts])
      simpa [h0] using h
    exact hOld τ0 hτ0 ⟨ha0,hb0,hc0⟩
  · have hb0 : m.b ∈ τ0.verts := by
      have h : t.b ∈ τ0.verts :=
        (hs0 t.b).2 (by simp [Move32Site.targetTet₀, Tet.verts])
      simpa [h1] using h
    exact hOld τ0 hτ0 ⟨ha0,hb0,hc0⟩
  · have hb1 : m.b ∈ τ1.verts := by
      have h : t.c ∈ τ1.verts :=
        (hs1 t.c).2 (by simp [Move32Site.targetTet₁, Tet.verts])
      simpa [h2] using h
    exact hOld τ1 hτ1 ⟨ha1,hb1,hc1⟩

/-- Source-face vertices of an exact-three second rim cannot include
any of the three old `2→3` face vertices. -/
theorem Move23Site.second_candidate_sourceFace_avoids_oldABC
    {K : Triangulation} (m : Move23Site) (s t : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hsd : s.d = m.a) (hse : s.e = m.b)
    (hslegal : s.LegalIn (m.replace K))
    (htd : t.d = m.a) (hte : t.e = m.c)
    (htrealized : t.RealizedIn (s.replace (m.replace K))) :
    ∀ y ∈ [t.a,t.b,t.c], y ≠ m.a ∧ y ≠ m.b ∧ y ≠ m.c := by
  have hb : m.b ∉ [t.a,t.b,t.c] :=
    m.second_candidate_sourceFace_not_contains_oldThird
      s t hcore hlegal hsd hse hslegal htd hte htrealized
  have hcore1 : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hcore2 : ClosedTriangulationCore (s.replace (m.replace K)) :=
    hcore1.move32Site_replace_closedCore s hslegal
  have hfive := hcore2.move32Site_distinct t htrealized
  have hnotD : t.d ∉ [t.a,t.b,t.c] := by
    simp at hfive ⊢
    aesop
  have hnotE : t.e ∉ [t.a,t.b,t.c] := by
    simp at hfive ⊢
    aesop
  intro y hy
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hnotD
    simpa [htd, h] using hy
  · intro h
    apply hb
    simpa [h] using hy
  · intro h
    apply hnotE
    simpa [hte, h] using hy

/-- Any transverse vertex of the second candidate, distinct from the two
old `2→3` external endpoints `d,e`, is outside the original five labels.
Neither a high-spoke condition nor the second move's legality is needed. -/
theorem Move23Site.second_candidate_third_fresh_original
    {K : Triangulation} (m : Move23Site) (s t : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hsd : s.d = m.a) (hse : s.e = m.b)
    (hslegal : s.LegalIn (m.replace K))
    (htd : t.d = m.a) (hte : t.e = m.c)
    (htrealized : t.RealizedIn (s.replace (m.replace K)))
    (y : Nat) (hy : y ∈ [t.a,t.b,t.c])
    (hyd : y ≠ m.d) (hye : y ≠ m.e) :
    y ∉ [m.a,m.b,m.c,m.d,m.e] := by
  obtain ⟨hya,hyb,hyc⟩ :=
    m.second_candidate_sourceFace_avoids_oldABC
      s t hcore hlegal hsd hse hslegal htd hte htrealized y hy
  intro hm
  simp only [List.mem_cons, List.mem_singleton, or_false] at hm
  rcases hm with h | h | h | h | h
  · exact hya h
  · exact hyb h
  · exact hyc h
  · exact hyd h
  · exact hye h

/-- The `2→3` new tetrahedron `{a,c,d,e}` survives any realized first
`3→2` on `(a,b)`: all three deleted tetrahedra contain `b`, whereas this
new tetrahedron does not. No second-site hypothesis is used. -/
theorem Move23Site.newTetOne_mem_after_first_move32
    {K : Triangulation} (m : Move23Site) (s : Move32Site)
    (hse : s.e = m.b) :
    m.newTet₁ ∈ (s.replace (m.replace K)).tets := by
  have hm := m.distinct
  have hnotb : m.b ∉ m.newTet₁.verts := by
    simp [Move23Site.newTet₁, Tet.verts] at hm ⊢
    aesop
  have htargetNot (target : Tet) (hs : s.e ∈ target.verts) :
      ¬ SameTetVertices m.newTet₁ target := by
    intro h
    have he : s.e ∈ m.newTet₁.verts := (h s.e).2 hs
    exact hnotb (by simpa [hse] using he)
  have hn0 : ¬ SameTetVertices m.newTet₁ s.targetTet₀ :=
    htargetNot _ (by simp [Move32Site.targetTet₀, Tet.verts])
  have hn1 : ¬ SameTetVertices m.newTet₁ s.targetTet₁ :=
    htargetNot _ (by simp [Move32Site.targetTet₁, Tet.verts])
  have hn2 : ¬ SameTetVertices m.newTet₁ s.targetTet₂ :=
    htargetNot _ (by simp [Move32Site.targetTet₂, Tet.verts])
  have hmem : m.newTet₁ ∈ (m.replace K).tets := by
    rw [m.replace_tets_eq K]
    simp
  have h0 := mem_eraseFirstSameTet_of_mem_of_not_same hmem hn0
  have h1 := mem_eraseFirstSameTet_of_mem_of_not_same h0 hn1
  have h2 := mem_eraseFirstSameTet_of_mem_of_not_same h1 hn2
  have hret : m.newTet₁ ∈ s.unchangedTets (m.replace K) := by
    simpa only [Move32Site.unchangedTets] using h2
  rw [s.replace_tets_eq]
  simp [hret]

/-- Saturation of the actual second candidate on `(a,c)` forces the
original new-edge endpoints `d,e` into its three-vertex source face.
There is no appeal to second `LegalIn`. -/
theorem Move23Site.second_candidate_sourceFace_contains_newEdgeEndpoints
    {K : Triangulation} (m : Move23Site) (s t : Move32Site)
    (hcore : ClosedTriangulationCore K)
    (hlegal : m.LegalIn K)
    (hslegal : s.LegalIn (m.replace K))
    (hse : s.e = m.b)
    (htd : t.d = m.a) (hte : t.e = m.c)
    (htrealized : t.RealizedIn (s.replace (m.replace K)))
    (htthree : t.SharedEdgeExactlyThree (s.replace (m.replace K))) :
    m.d ∈ [t.a,t.b,t.c] ∧ m.e ∈ [t.a,t.b,t.c] := by
  have hcore1 : ClosedTriangulationCore (m.replace K) :=
    hcore.move23Site_replace_closedCore m hlegal
  have hcore2 : ClosedTriangulationCore (s.replace (m.replace K)) :=
    hcore1.move32Site_replace_closedCore s hslegal
  have hmem : m.newTet₁ ∈ (s.replace (m.replace K)).tets :=
    m.newTetOne_mem_after_first_move32 s hse
  have hshared :=
    hcore2.move32Site_same_target_of_contains_sharedEdge_of_realized_exactlyThree
      t htrealized htthree hmem
      (by simp [Move23Site.newTet₁, Tet.verts, htd])
      (by simp [Move23Site.newTet₁, Tet.verts, hte])
  have hsource {v : Nat} (hv : v ∈ m.newTet₁.verts)
      (hva : v ≠ m.a) (hvc : v ≠ m.c) :
      v ∈ [t.a,t.b,t.c] := by
    rcases hshared with h0 | h1 | h2
    · have h := (h0 v).1 hv
      simp only [Move32Site.targetTet₀, Tet.verts,
        List.mem_cons, List.mem_singleton, or_false] at h
      rw [htd, hte] at h
      simp only [List.mem_cons, List.mem_singleton, or_false]
      aesop
    · have h := (h1 v).1 hv
      simp only [Move32Site.targetTet₁, Tet.verts,
        List.mem_cons, List.mem_singleton, or_false] at h
      rw [htd, hte] at h
      simp only [List.mem_cons, List.mem_singleton, or_false]
      aesop
    · have h := (h2 v).1 hv
      simp only [Move32Site.targetTet₂, Tet.verts,
        List.mem_cons, List.mem_singleton, or_false] at h
      rw [htd, hte] at h
      simp only [List.mem_cons, List.mem_singleton, or_false]
      aesop
  have hm := m.distinct
  simp at hm
  constructor
  · apply hsource
    · simp [Move23Site.newTet₁, Tet.verts]
    · aesop
    · aesop
  · apply hsource
    · simp [Move23Site.newTet₁, Tet.verts]
    · aesop
    · aesop

end Poincare

#print axioms Poincare.Move23Site.old_sharedFace_absent_after_first_move32
#print axioms Poincare.Move23Site.second_candidate_sourceFace_not_contains_oldThird
#print axioms Poincare.Move23Site.second_candidate_sourceFace_avoids_oldABC
#print axioms Poincare.Move23Site.second_candidate_third_fresh_original
#print axioms Poincare.Move23Site.newTetOne_mem_after_first_move32
#print axioms Poincare.Move23Site.second_candidate_sourceFace_contains_newEdgeEndpoints