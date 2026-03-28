import Mathlib
import Poincare.GreedyTermination

namespace Poincare

section GreedyDescentCorrectness

variable {ι : Type*} [DecidableEq ι]

abbrev GreedyState := ι → ℤ

theorem greedy_descent_correct_final
    (support : Finset ι)
    (step : GreedyState ι → GreedyState ι)
    (terminal : GreedyState ι → Prop)
    (hdesc : ∀ x, ¬ terminal x → Φ support (step x) < Φ support x)
    (hfix : ∀ x, terminal x → step x = x) :
    ∀ x, ∃ n,
      terminal (Nat.iterate step n x) ∧
      Nat.iterate step (n + 1) x = Nat.iterate step n x := by
  intro x
  obtain ⟨n, hn⟩ := greedy_descent_terminates
    (support := support) (step := step) (terminal := terminal) hdesc x
  refine ⟨n, hn, ?_⟩
  have hfixed : step (Nat.iterate step n x) = Nat.iterate step n x := hfix _ hn
  simpa [Nat.iterate_succ] using hfixed

end GreedyDescentCorrectness

end Poincare
