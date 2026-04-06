import Mathlib
import Poincare.ZeroDefectCharacterization

namespace Poincare

axiom step : Triangulation → Triangulation
axiom step_strict :
  ∀ T : Triangulation, Phi T > 0 → Phi (step T) < Phi T

theorem termination_conditional :
  ∀ T : Triangulation, ∃ n : Nat, Phi ((step^[n]) T) = 0 := by
  suffices hmain : ∀ m : Nat, ∀ T : Triangulation, Phi T ≤ m → ∃ n : Nat, Phi ((step^[n]) T) = 0 by
    intro T
    exact hmain (Phi T) T le_rfl
  intro m
  induction' m with m hm
  · intro T hle
    have hzero : Phi T = 0 := Nat.eq_zero_of_le_zero hle
    exact ⟨0, by simp [hzero]⟩
  · intro T hle
    by_cases hzero : Phi T = 0
    · exact ⟨0, by simp [hzero]⟩
    · have hpos : Phi T > 0 := Nat.pos_of_ne_zero hzero
      have hlt : Phi (step T) < Phi T := step_strict T hpos
      have hle' : Phi (step T) ≤ m := Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hle)
      obtain ⟨n, hn⟩ := hm (step T) hle'
      exact ⟨n + 1, by
        simpa [Function.iterate_succ_apply, Function.comp] using hn
      ⟩

end Poincare
