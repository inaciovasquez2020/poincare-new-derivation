import Poincare.Move32SurvivorClassification
import Lean

namespace BlockerAudit

def represented (K : List (List Nat)) (q : List Nat) : Prop :=
  ∃ tet ∈ K, ∀ w ∈ q, w ∈ tet

def excess (K : List (List Nat)) (x z : Nat) (q : List Nat) : Prop :=
  x ∉ q ∧ z ∉ q ∧ represented K (x :: q) ∧
    represented K (z :: q) ∧ ¬ represented K (x :: z :: q)

theorem move32_excess_iff
    (R : List (List Nat)) (x y a b c z : Nat) (q : List Nat)
    (hd : [x, y, a, b, c, z].Nodup)
    (hstar : ∀ tet ∈ R, ¬ (x ∈ tet ∧ y ∈ tet))
    (habs : ¬ represented R [a, b, c]) :
    let K := [x,y,a,b] :: [x,y,a,c] :: [x,y,b,c] :: R
    let L := [x,a,b,c] :: [y,a,b,c] :: R
    excess L x z q ↔ excess K x z q ∧ y ∉ q := by
  let K := [x,y,a,b] :: [x,y,a,c] :: [x,y,b,c] :: R
  let L := [x,a,b,c] :: [y,a,b,c] :: R
  change excess L x z q ↔ excess K x z q ∧ y ∉ q
  simp at hd
  have hz (s : List Nat) :
      represented K (z :: s) ↔ represented L (z :: s) := by
    simp [K, L, represented, List.mem_cons] at *
    grind
  have hxz : represented K (x :: z :: q) ↔ represented L (x :: z :: q) := by
    simpa [represented, List.mem_cons, and_assoc, and_left_comm, and_comm] using hz (x :: q)
  have noTriangle (h : represented L (z :: q)) :
      ¬ (a ∈ q ∧ b ∈ q ∧ c ∈ q) := by
    intro ⟨ha,hb,hc⟩
    apply habs
    rcases h with ⟨t, ht, hsub⟩
    have hzt := hsub z (by simp)
    have hmem : t ∈ R := by
      simp [L, List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · simp at hzt
        grind
      · simp at hzt
        grind
      · exact ht
    exact ⟨t, hmem, by
      intro w hw
      simp at hw
      rcases hw with rfl | rfl | rfl <;> apply hsub <;> simp_all⟩
  have new_to_old (h : represented L (x :: q)) (hn : ¬ (a ∈ q ∧ b ∈ q ∧ c ∈ q)) :
      represented K (x :: q) ∧ y ∉ q := by
    rcases h with ⟨t, ht, hsub⟩
    have hxt := hsub x (by simp)
    simp [L, List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · have hq (w : Nat) (hw : w ∈ q) := hsub w (by simp [hw])
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      refine ⟨?_, ?_⟩
      · by_cases ha : a ∈ q
        · by_cases hb : b ∈ q
          · refine ⟨[x,y,a,b], by simp [K], ?_⟩
            intro w hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at *
            grind
          · refine ⟨[x,y,a,c], by simp [K], ?_⟩
            intro w hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at *
            grind
        · refine ⟨[x,y,b,c], by simp [K], ?_⟩
          intro w hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at *
          grind
      · intro hy
        specialize hq y hy
        grind
    · simp at hxt
      grind
    · refine ⟨⟨t, by simp [K, ht], hsub⟩, ?_⟩
      intro hy
      exact hstar t ht ⟨hxt, hsub y (by simp [hy])⟩
  have old_to_new (h : represented K (x :: q)) (hy : y ∉ q) :
      represented L (x :: q) := by
    rcases h with ⟨t, ht, hsub⟩
    simp [K, List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | ht
    · refine ⟨[x,a,b,c], by simp [L], ?_⟩
      intro w hw
      have hh := hsub w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at *
      grind
    · refine ⟨[x,a,b,c], by simp [L], ?_⟩
      intro w hw
      have hh := hsub w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at *
      grind
    · refine ⟨[x,a,b,c], by simp [L], ?_⟩
      intro w hw
      have hh := hsub w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at *
      grind
    · exact ⟨t, by simp [L, ht], hsub⟩
  constructor
  · rintro ⟨hx, hzq, hLx, hLz, hLxz⟩
    obtain ⟨hKx, hy⟩ := new_to_old hLx (noTriangle hLz)
    exact ⟨⟨hx, hzq, hKx, (hz q).2 hLz, fun h => hLxz (hxz.1 h)⟩, hy⟩
  · rintro ⟨⟨hx, hzq, hKx, hKz, hKxz⟩, hy⟩
    exact ⟨hx, hzq, old_to_new hKx hy, (hz q).1 hKz, fun h => hKxz (hxz.2 h)⟩

end BlockerAudit

namespace Poincare

open BlockerAudit

private theorem represented_cons (tet : List Nat) (R : List (List Nat)) (q : List Nat) :
    represented (tet :: R) q ↔ (∀ w ∈ q, w ∈ tet) ∨ represented R q := by
  constructor
  · rintro ⟨t, ht, hq⟩
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Or.inl hq
    · exact Or.inr ⟨t, ht, hq⟩
  · rintro (hq | ⟨t, ht, hq⟩)
    · exact ⟨tet, List.mem_cons_self, hq⟩
    · exact ⟨t, List.mem_cons_of_mem _ ht, hq⟩

private theorem represented_map_verts (tets : List Tet) (q : List Nat) :
    represented (tets.map Tet.verts) q ↔
      ∃ t ∈ tets, ∀ w ∈ q, w ∈ t.verts := by
  constructor
  · rintro ⟨vs, hvs, hq⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hvs
    exact ⟨t, ht, hq⟩
  · rintro ⟨t, ht, hq⟩
    exact ⟨t.verts, List.mem_map.mpr ⟨t, ht, rfl⟩, hq⟩

private theorem represented_congr (A B : List Tet)
    (hAB : ∀ t ∈ A, ∃ r ∈ B, SameTetVertices t r)
    (hBA : ∀ r ∈ B, ∃ t ∈ A, SameTetVertices r t) (q : List Nat) :
    represented (A.map Tet.verts) q ↔ represented (B.map Tet.verts) q := by
  rw [represented_map_verts, represented_map_verts]
  constructor
  · rintro ⟨t, ht, hq⟩
    obtain ⟨r, hr, hsame⟩ := hAB t ht
    exact ⟨r, hr, fun w hw => (hsame w).1 (hq w hw)⟩
  · rintro ⟨r, hr, hq⟩
    obtain ⟨t, ht, hsame⟩ := hBA r hr
    exact ⟨t, ht, fun w hw => (hsame w).1 (hq w hw)⟩

private theorem Move32Site.represented_target_cluster
    {K : Triangulation} (hcore : ClosedTriangulationCore K) (s : Move32Site)
    (hlegal : s.LegalIn K) (q : List Nat) :
    represented (K.tets.map Tet.verts) q ↔
      represented ((s.targetTet₀ :: s.targetTet₁ :: s.targetTet₂ ::
        s.unchangedTets K).map Tet.verts) q := by
  apply represented_congr
  · intro t ht
    by_cases h : s.d ∈ t.verts ∧ s.e ∈ t.verts
    · rcases hcore.move32Site_same_target_of_contains_sharedEdge s hlegal ht h.1 h.2
        with h₀ | h₁ | h₂
      · exact ⟨s.targetTet₀, by simp, h₀⟩
      · exact ⟨s.targetTet₁, by simp, h₁⟩
      · exact ⟨s.targetTet₂, by simp, h₂⟩
    · have keep (r : Tet) (hd : s.d ∈ r.verts) (he : s.e ∈ r.verts) :
          ¬ SameTetVertices t r := by
        intro heq
        exact h ⟨(heq _).2 hd, (heq _).2 he⟩
      have h₀ := keep s.targetTet₀ (by simp [Move32Site.targetTet₀, Tet.verts])
        (by simp [Move32Site.targetTet₀, Tet.verts])
      have h₁ := keep s.targetTet₁ (by simp [Move32Site.targetTet₁, Tet.verts])
        (by simp [Move32Site.targetTet₁, Tet.verts])
      have h₂ := keep s.targetTet₂ (by simp [Move32Site.targetTet₂, Tet.verts])
        (by simp [Move32Site.targetTet₂, Tet.verts])
      have hmem : t ∈ s.unchangedTets K :=
        mem_eraseFirstSameTet_of_mem_of_not_same
          (mem_eraseFirstSameTet_of_mem_of_not_same
            (mem_eraseFirstSameTet_of_mem_of_not_same ht h₀) h₁) h₂
      exact ⟨t, by simp [hmem], sameTetVertices_refl t⟩
  · intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | ht
    · obtain ⟨r, hr, heq⟩ := hlegal.1.1
      exact ⟨r, hr, sameTetVertices_symm heq⟩
    · obtain ⟨r, hr, heq⟩ := hlegal.1.2.1
      exact ⟨r, hr, sameTetVertices_symm heq⟩
    · obtain ⟨r, hr, heq⟩ := hlegal.1.2.2
      exact ⟨r, hr, sameTetVertices_symm heq⟩
    · exact ⟨t, s.mem_original_of_mem_unchanged ht, sameTetVertices_refl t⟩

theorem Move32Site.excess_iff_of_outside
    {K : Triangulation} (hcore : ClosedTriangulationCore K) (s : Move32Site)
    (hlegal : s.LegalIn K) (z : Nat) (q : List Nat)
    (hd : [s.d, s.e, s.a, s.b, s.c, z].Nodup) :
    excess ((s.replace K).tets.map Tet.verts) s.d z q ↔
      excess (K.tets.map Tet.verts) s.d z q ∧ s.e ∉ q := by
  let R := (s.unchangedTets K).map Tet.verts
  have hstar : ∀ t ∈ R, ¬ (s.d ∈ t ∧ s.e ∈ t) := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
    exact hcore.move32Site_unchangedTet_not_contains_sharedEdge s hlegal hr
  have habs : ¬ represented R [s.a, s.b, s.c] := by
    rw [represented_map_verts]
    rintro ⟨t, ht, hq⟩
    exact hlegal.2.2 t (s.mem_original_of_mem_unchanged ht)
      ⟨hq _ (by simp), hq _ (by simp), hq _ (by simp)⟩
  have repr (l : List Nat) :
      represented (K.tets.map Tet.verts) l ↔
        represented ([s.d,s.e,s.a,s.b] :: [s.d,s.e,s.a,s.c] ::
          [s.d,s.e,s.b,s.c] :: R) l := by
    rw [s.represented_target_cluster hcore hlegal]
    simp only [List.map_cons, Move32Site.targetTet₀, Move32Site.targetTet₁,
      Move32Site.targetTet₂, Tet.verts, R, represented_cons, List.mem_cons, List.not_mem_nil,
      or_comm, or_left_comm, or_assoc]
  have hnew (l : List Nat) :
      represented ((s.replace K).tets.map Tet.verts) l ↔
        represented ([s.d,s.a,s.b,s.c] :: [s.e,s.a,s.b,s.c] :: R) l := by
    rw [s.replace_tets_eq K]
    simp only [List.map_cons, Move32Site.sourceTet₀, Move32Site.sourceTet₁,
      Tet.verts, R, represented_cons, List.mem_cons, List.not_mem_nil,
      or_comm, or_left_comm, or_assoc]
  simpa only [excess, ← repr, ← hnew] using
    (move32_excess_iff R s.d s.e s.a s.b s.c z q hd hstar habs)

#print axioms Move32Site.excess_iff_of_outside

end Poincare
