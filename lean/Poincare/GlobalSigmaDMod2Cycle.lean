import Mathlib.Tactic
import Poincare.Triangulation

namespace Poincare

/-- The four triangular faces of an abstract tetrahedron. -/
def sigmaD (a b c d : Nat) : Finset (Finset Nat) :=
  {{a, b, c}, {a, b, d}, {a, c, d}, {b, c, d}}

/-- Every edge is incident to an even number of the four faces. -/
theorem sigmaD_isCycle_edges {a b c d : Nat}
    (hn : [a, b, c, d].Nodup) :
    ∀ g : Finset Nat, g.card = 2 →
      ((sigmaD a b c d).filter fun f => g ⊆ f).card % 2 = 0 := by
  classical
  have hdistinct :
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, not_or] at hn
    aesop
  rcases hdistinct with ⟨hab, hac, had, hbc, hbd, hcd⟩
  let S : Finset Nat := {a, b, c, d}
  have hcardS : S.card = 4 := by
    simp [S, hab, hac, had, hbc, hbd, hcd]
  have hSigma : sigmaD a b c d = S.powersetCard 3 := by
    simp [S, sigmaD, Finset.powersetCard_succ_insert,
      hab, hac, had, hbc, hbd, hcd,
      Finset.insert_comm, Finset.insert_assoc]
  intro g hg
  rw [hSigma]
  by_cases hsub : g ⊆ S
  · have hcard :
        ((S.powersetCard 3).filter (fun f => g ⊆ f)).card = 2 := by
      rw [Finset.card_filter_powersetCard_subset g S 3 hsub (by omega)]
      rw [hcardS, hg]
      norm_num
    rw [hcard]
    norm_num
  · have hempty : (S.powersetCard 3).filter (fun f => g ⊆ f) = ∅ := by
      ext f
      simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
      intro hf
      exact hsub (hf.2.trans (Finset.mem_powersetCard.mp hf.1).1)
    rw [hempty]
    norm_num

end Poincare
