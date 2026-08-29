import Poincare.GlobalMove32ReentryPolygonalLoop

namespace Poincare

/--
For an ordered concatenation of `m > 0` transition arcs, the endpoint of the
first transition occurs at the exact dyadic parameter `1 / 2^(m-1)`.

This is the missing path-evaluation companion to the existing arithmetic
result placing dyadic breakpoints on refined square-grid vertices.  It makes no
claim about the filling labels or about `Poincare.JIID`.
-/
theorem orderedTransitionPath_first_target_dyadic_probe
    {X : Type*} [TopologicalSpace X]
    (p : Nat → X)
    (arc : ∀ n, Path (p n) (p (n + 1)))
    (m : Nat) :
    0 < m →
      ∃ u : unitInterval,
        (u : ℝ) = 1 / (2 : ℝ) ^ (m - 1) ∧
        orderedTransitionPath p arc m u = p 1 := by
  induction m with
  | zero =>
      intro hm
      omega
  | succ m ih =>
      intro hm
      cases m with
      | zero =>
          refine ⟨(1 : unitInterval), ?_, ?_⟩
          · norm_num
          · simp [orderedTransitionPath]
      | succ n =>
          have hprev : 0 < Nat.succ n := by
            omega
          obtain ⟨v, hv, hpath⟩ := ih hprev

          let u : unitInterval :=
            ⟨(v : ℝ) / 2, by
              constructor
              · have hv0 := v.property.1
                linarith
              · have hv1 := v.property.2
                linarith⟩

          have hv' :
              (v : ℝ) = 1 / (2 : ℝ) ^ n := by
            simpa using hv

          have hu :
              (u : ℝ) = 1 / (2 : ℝ) ^ (Nat.succ n) := by
            dsimp [u]
            rw [hv', pow_succ]
            ring

          have huHalf : (u : ℝ) ≤ 1 / 2 := by
            dsimp [u]
            have hv1 := v.property.2
            linarith

          refine ⟨u, ?_, ?_⟩
          · simpa using hu
          · rw [orderedTransitionPath, Path.trans_apply]
            split_ifs with hhalf
            · simpa [u] using hpath
            · exact (hhalf huHalf).elim

end Poincare
