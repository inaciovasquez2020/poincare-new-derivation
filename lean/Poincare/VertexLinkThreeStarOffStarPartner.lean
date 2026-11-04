import Poincare.VertexLinkThreeStarPerimeterCoverage
import Mathlib.Tactic

namespace Poincare

/--
Every perimeter edge of a represented vertex-link star has exactly one
off-star partner triangle. This follows from closed-core incidence two,
distinct represented triangle vertex supports, and the fact that a
perimeter edge does not contain the star center.

No assumption about off-star connected components is used.
-/
theorem ClosedTriangulationCore.perimeterEdge_exists_unique_offStar_partner
    {K : Triangulation}
    (hcore : ClosedTriangulationCore K)
    (v x : Nat)
    (e : LinkEdge)
    (hperimeter :
      (∃ σ ∈ vertexLinkStarTriangles K v x, e.InTriangle σ) ∧
        ¬ (x = e.lo ∨ x = e.hi)) :
    ∃! ρ : LinkTriangle,
      ρ ∈ vertexLinkTriangles K v ∧
      e.InTriangle ρ ∧
      ρ ∉ vertexLinkStarTriangles K v x := by
  classical
  obtain ⟨⟨σ, hσstar, heσ⟩, hnoX⟩ := hperimeter
  have hσdata := (mem_vertexLinkStarTriangles_iff K v x σ).1 hσstar
  have hnotLo : x ≠ e.lo := fun h => hnoX (Or.inl h)
  have hnotHi : x ≠ e.hi := fun h => hnoX (Or.inr h)
  have hlohi : e.lo ≠ e.hi := Nat.ne_of_lt e.sorted

  have hcomplete
      (τ : LinkTriangle)
      (hτ : τ ∈ vertexLinkTriangles K v)
      (hxτ : x ∈ τ.verts)
      (heτ : e.InTriangle τ) :
      ∀ y : Nat, y ∈ τ.verts ↔
        y = x ∨ y = e.lo ∨ y = e.hi := by
    have hτnodup :=
      vertexLinkTriangles_triangle_nodup K hcore v τ hτ
    have hTcard : τ.verts.toFinset.card = 3 := by
      rw [List.toFinset_card_of_nodup hτnodup]
      rfl
    have hTripCard :
        ({x, e.lo, e.hi} : Finset Nat).card = 3 := by
      simp [hnotLo, hnotHi, hlohi]
    have hSub :
        ({x, e.lo, e.hi} : Finset Nat) ⊆
          τ.verts.toFinset := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact List.mem_toFinset.mpr hxτ
      · exact List.mem_toFinset.mpr heτ.1
      · exact List.mem_toFinset.mpr heτ.2
    have hEq : ({x, e.lo, e.hi} : Finset Nat) =
        τ.verts.toFinset := by
      apply Finset.eq_of_subset_of_card_le hSub
      rw [hTcard, hTripCard]
    intro y
    calc
      y ∈ τ.verts ↔ y ∈ τ.verts.toFinset := List.mem_toFinset
      _ ↔ y ∈ ({x, e.lo, e.hi} : Finset Nat) := by rw [hEq]
      _ ↔ y = x ∨ y = e.lo ∨ y = e.hi := by simp

  have hpair_mem :
      ∀ (l : List LinkTriangle), l.Pairwise
        (fun τ ρ =>
          ¬ ∀ y : Nat, y ∈ τ.verts ↔ y ∈ ρ.verts) →
        ∀ {a b : LinkTriangle},
          a ∈ l → b ∈ l → a ≠ b →
          ¬ ∀ y : Nat, y ∈ a.verts ↔ y ∈ b.verts := by
    intro l hp
    induction hp with
    | nil =>
        intro a b ha hb hne
        simp at ha
    | @cons c l hhead htail ih =>
        intro a b ha hb hne
        have hsymm : ∀ {d f : LinkTriangle},
            (¬ ∀ y : Nat, y ∈ d.verts ↔ y ∈ f.verts) →
            (¬ ∀ y : Nat, y ∈ f.verts ↔ y ∈ d.verts) := by
          intro d f h hs
          exact h (fun y => (hs y).symm)
        rcases List.mem_cons.mp ha with rfl | haTail
        · have hbTail : b ∈ l := by
            rcases List.mem_cons.mp hb with h | h
            · exact (hne h.symm).elim
            · exact h
          exact hhead b hbTail
        · rcases List.mem_cons.mp hb with rfl | hbTail
          · exact hsymm (hhead a haTail)
          · exact ih haTail hbTail hne

  have hstarUnique
      (τ : LinkTriangle)
      (hτstar : τ ∈ vertexLinkStarTriangles K v x)
      (heτ : e.InTriangle τ) : τ = σ := by
    have hτdata := (mem_vertexLinkStarTriangles_iff K v x τ).1 hτstar
    by_contra hneq
    have hEq : ∀ y : Nat,
        y ∈ τ.verts ↔ y ∈ σ.verts := by
      intro y
      exact
        (hcomplete τ hτdata.1 hτdata.2 heτ y).trans
          (hcomplete σ hσdata.1 hσdata.2 heσ y).symm
    exact
      (hpair_mem (vertexLinkTriangles K v)
        (vertexLinkTriangles_pairwise_vertexSet_ne K hcore v)
        hτdata.1 hσdata.1 hneq) hEq

  have hrep : e.RepresentedAt K v :=
    ⟨σ, hσdata.1, heσ⟩
  have hinc :
      ((vertexLinkTriangles K v).filter
        (fun τ => decide (e.InTriangle τ))).length = 2 :=
    represented_linkEdge_link_incidence_two K hcore v e hrep
  obtain ⟨p, q, htwo⟩ := List.length_eq_two.mp hinc
  have hnodup :
      (vertexLinkTriangles K v).Nodup :=
    vertexLinkTriangles_nodup K hcore v
  have hpq : p ≠ q := by
    have hn := hnodup.filter (fun τ => decide (e.InTriangle τ))
    rw [htwo] at hn
    simpa using hn
  have hpdata : p ∈ vertexLinkTriangles K v ∧ e.InTriangle p := by
    have h : p ∈ (vertexLinkTriangles K v).filter
        (fun τ => decide (e.InTriangle τ)) := by
      rw [htwo]
      simp
    simpa using (List.mem_filter.mp h)
  have hqdata : q ∈ vertexLinkTriangles K v ∧ e.InTriangle q := by
    have h : q ∈ (vertexLinkTriangles K v).filter
        (fun τ => decide (e.InTriangle τ)) := by
      rw [htwo]
      simp
    simpa using (List.mem_filter.mp h)
  have hσfilter : σ ∈ (vertexLinkTriangles K v).filter
      (fun τ => decide (e.InTriangle τ)) := by
    simp [hσdata.1, heσ]
  rw [htwo] at hσfilter
  have hσcases : σ = p ∨ σ = q := by
    simpa using hσfilter
  rcases hσcases with hsp | hsq
  · subst p
    have hqoff : q ∉ vertexLinkStarTriangles K v x := by
      intro hqstar
      have hqeq := hstarUnique q hqstar hqdata.2
      exact hpq hqeq.symm
    refine ⟨q, ⟨hqdata.1, hqdata.2, hqoff⟩, ?_⟩
    intro τ hτ
    have hτfilter : τ ∈ (vertexLinkTriangles K v).filter
        (fun t => decide (e.InTriangle t)) := by
      simp [hτ.1, hτ.2.1]
    rw [htwo] at hτfilter
    rcases (by simpa using hτfilter : τ = σ ∨ τ = q) with h | h
    · subst τ
      exact (hτ.2.2 hσstar).elim
    · exact h
  · subst q
    have hpoff : p ∉ vertexLinkStarTriangles K v x := by
      intro hpstar
      have hpeq := hstarUnique p hpstar hpdata.2
      exact hpq hpeq
    refine ⟨p, ⟨hpdata.1, hpdata.2, hpoff⟩, ?_⟩
    intro τ hτ
    have hτfilter : τ ∈ (vertexLinkTriangles K v).filter
        (fun t => decide (e.InTriangle t)) := by
      simp [hτ.1, hτ.2.1]
    rw [htwo] at hτfilter
    rcases (by simpa using hτfilter : τ = p ∨ τ = σ) with h | h
    · exact h
    · subst τ
      exact (hτ.2.2 hσstar).elim

end Poincare
