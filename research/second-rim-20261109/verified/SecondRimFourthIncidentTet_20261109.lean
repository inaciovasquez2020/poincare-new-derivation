import Poincare.Triangulation

/-! Extract a fourth distinct actual tetrahedron from incidence >=4.
The `K.tets.Nodup` premise is necessary: repeated list entries otherwise
make the statement false.  No manifold or `Move32Site` assumptions. -/

namespace Poincare
namespace SecondRimFourthIncidentTet

/-! Local Init-only nodup preservation under filtering. -/
private theorem nodup_filter_init
    {α : Type} (p : α → Prop) [DecidablePred p] :
    ∀ xs : List α, xs.Nodup → (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x ys ih =>
      intro hxs
      have hnot : x ∉ ys := (List.nodup_cons.mp hxs).1
      have htail : ys.Nodup := (List.nodup_cons.mp hxs).2
      by_cases hx : p x
      · have hnotFilter : x ∉ ys.filter p := by
          intro h
          exact hnot (List.mem_filter.mp h).1
        have hcons : (x :: ys.filter p).Nodup :=
          List.nodup_cons.mpr ⟨hnotFilter, ih htail⟩
        simpa [List.filter_cons, hx] using hcons
      · simpa [List.filter_cons, hx] using ih htail

private theorem nodup_cover_one {α : Type} (l : List α) (a : α)
    (hn : l.Nodup) (hc : ∀ x ∈ l, x = a) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons x xs =>
      have hx : x = a := hc x (by simp)
      have hnot : x ∉ xs := (List.nodup_cons.mp hn).1
      have hnil : xs = [] := by
        cases xs with
        | nil => rfl
        | cons y ys =>
            have hy : y = a := hc y (by simp)
            have hmem : x ∈ y :: ys := by simp [hx, hy]
            exact False.elim (hnot hmem)
      simp [hnil]

private theorem nodup_cover_two {α : Type} (l : List α) (a b : α)
    (hn : l.Nodup) (hc : ∀ x ∈ l, x = a ∨ x = b) : l.length ≤ 2 := by
  cases l with
  | nil => simp
  | cons x xs =>
      have hnot : x ∉ xs := (List.nodup_cons.mp hn).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hn).2
      have hx : x = a ∨ x = b := hc x (by simp)
      rcases hx with ha | hb
      · have hs : ∀ y ∈ xs, y = b := by
          intro y hy
          rcases hc y (by simp [hy]) with hya | hyb
          · have hxmem : x ∈ xs := by simpa [ha, hya] using hy
            exact False.elim (hnot hxmem)
          · exact hyb
        simpa using Nat.succ_le_succ (nodup_cover_one xs b hxs hs)
      · have hs : ∀ y ∈ xs, y = a := by
          intro y hy
          rcases hc y (by simp [hy]) with hya | hyb
          · exact hya
          · have hxmem : x ∈ xs := by simpa [hb, hyb] using hy
            exact False.elim (hnot hxmem)
        simpa using Nat.succ_le_succ (nodup_cover_one xs a hxs hs)

private theorem nodup_cover_three {α : Type} (l : List α) (a b c : α)
    (hn : l.Nodup) (hc : ∀ x ∈ l, x = a ∨ x = b ∨ x = c) :
    l.length ≤ 3 := by
  cases l with
  | nil => simp
  | cons x xs =>
      have hnot : x ∉ xs := (List.nodup_cons.mp hn).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hn).2
      have hx : x = a ∨ x = b ∨ x = c := hc x (by simp)
      rcases hx with ha | hb | hc'
      · have hs : ∀ y ∈ xs, y = b ∨ y = c := by
          intro y hy
          rcases hc y (by simp [hy]) with hya | hyb | hyc
          · have hxmem : x ∈ xs := by simpa [ha, hya] using hy
            exact False.elim (hnot hxmem)
          · exact Or.inl hyb
          · exact Or.inr hyc
        simpa using Nat.succ_le_succ (nodup_cover_two xs b c hxs hs)
      · have hs : ∀ y ∈ xs, y = a ∨ y = c := by
          intro y hy
          rcases hc y (by simp [hy]) with hya | hyb | hyc
          · exact Or.inl hya
          · have hxmem : x ∈ xs := by simpa [hb, hyb] using hy
            exact False.elim (hnot hxmem)
          · exact Or.inr hyc
        simpa using Nat.succ_le_succ (nodup_cover_two xs a c hxs hs)
      · have hs : ∀ y ∈ xs, y = a ∨ y = b := by
          intro y hy
          rcases hc y (by simp [hy]) with hya | hyb | hyc
          · exact Or.inl hya
          · exact Or.inr hyb
          · have hxmem : x ∈ xs := by simpa [hc', hyc] using hy
            exact False.elim (hnot hxmem)
        simpa using Nat.succ_le_succ (nodup_cover_two xs a b hxs hs)

/-- Distinct fourth represented tetrahedron from a length >= 4 edge-star list.
    Does not assume the three named tetrahedra are members (stronger result). -/
theorem fourth_incident_of_incidence_four
    (K : Triangulation) (a d : Nat) (τ₀ τ₁ τ₂ : Tet)
    (hnd : K.tets.Nodup)
    (hinc : 4 ≤ (K.tets.filter (fun τ =>
      a ∈ τ.verts ∧ d ∈ τ.verts)).length) :
    ∃ τ ∈ K.tets,
      a ∈ τ.verts ∧ d ∈ τ.verts ∧
      τ ≠ τ₀ ∧ τ ≠ τ₁ ∧ τ ≠ τ₂ := by
  classical
  let L := K.tets.filter (fun τ => a ∈ τ.verts ∧ d ∈ τ.verts)
  have hLnd : L.Nodup := by
    dsimp [L]
    exact nodup_filter_init
      (fun τ : Tet => a ∈ τ.verts ∧ d ∈ τ.verts)
      K.tets hnd
  apply Classical.byContradiction
  intro hno
  have hcover : ∀ τ ∈ L, τ = τ₀ ∨ τ = τ₁ ∨ τ = τ₂ := by
    intro τ ht
    have hdata : τ ∈ K.tets ∧ a ∈ τ.verts ∧ d ∈ τ.verts := by
      simpa [L] using ht
    by_cases h0 : τ = τ₀
    · exact Or.inl h0
    by_cases h1 : τ = τ₁
    · exact Or.inr (Or.inl h1)
    by_cases h2 : τ = τ₂
    · exact Or.inr (Or.inr h2)
    exact False.elim (hno ⟨τ, hdata.1, hdata.2.1,
      hdata.2.2, h0, h1, h2⟩)
  have hbound : L.length ≤ 3 :=
    nodup_cover_three L τ₀ τ₁ τ₂ hLnd hcover
  have hfour : 4 ≤ L.length := hinc
  have hbad : 4 ≤ (3 : Nat) := Nat.le_trans hfour hbound
  exact (by decide : ¬ 4 ≤ (3 : Nat)) hbad

end SecondRimFourthIncidentTet
end Poincare

#print axioms Poincare.SecondRimFourthIncidentTet.fourth_incident_of_incidence_four