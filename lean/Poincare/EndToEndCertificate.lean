import Mathlib
import Poincare.GreedyTermination
import Poincare.GreedyDescentCorrectness

namespace Poincare

section EndToEnd

variable {ι : Type*} [DecidableEq ι]

abbrev GreedyState := ι → ℤ

def cert (support : Finset ι) (x : GreedyState) : ℕ :=
  Φ support x

theorem terminal_iff_cert_zero
    (support : Finset ι)
    (terminal : GreedyState → Prop)
    (hzero_to_terminal : ∀ x, cert support x = 0 → terminal x)
    (hterminal_to_zero : ∀ x, terminal x → cert support x = 0) :
    ∀ x, terminal x ↔ cert support x = 0 := by
  intro x
  constructor
  · exact hterminal_to_zero x
  · exact hzero_to_terminal x

theorem end_to_end_correctness
    (support : Finset ι)
    (step : GreedyState → GreedyState)
    (terminal : GreedyState → Prop)
    (hdesc : ∀ x, ¬ terminal x → Φ support (step x) < Φ support x)
    (hfix : ∀ x, terminal x → step x = x)
    (hzero_to_terminal : ∀ x, cert support x = 0 → terminal x)
    (hterminal_to_zero : ∀ x, terminal x → cert support x = 0) :
    ∀ x, ∃ n,
      Nat.iterate step (n + 1) x = Nat.iterate step n x ∧
      cert support (Nat.iterate step n x) = 0 := by
  intro x
  obtain ⟨n, hn_term, hn_fix⟩ :=
    greedy_descent_correct_final
      (support := support)
      (step := step)
      (terminal := terminal)
      hdesc hfix x
  refine ⟨n, hn_fix, ?_⟩
  exact hterminal_to_zero _ hn_term

end EndToEnd

end Poincare
