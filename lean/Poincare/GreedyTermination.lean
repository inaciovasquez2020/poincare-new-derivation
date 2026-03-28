import Mathlib
import Poincare.AbsInequality

open scoped BigOperators

namespace Poincare

abbrev GreedyState (ι : Type*) [DecidableEq ι] := ι → ℤ

section GreedyTermination

variable {ι : Type*} [DecidableEq ι]

def Φ (s : Finset ι) (x : GreedyState ι) : ℕ :=
  Int.toNat (∑ j in s, |x j|)

theorem Phi_lt_of_sum_abs_lt
    {s : Finset ι} {x y : GreedyState ι}
    (h : (∑ j in s, |y j|) < ∑ j in s, |x j|) :
    Φ s y < Φ s x := by
  unfold Φ
  refine Int.toNat_lt_toNat ?_ ?_ h
  · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem Phi_update_lt_of_descent
    {s : Finset ι} {x : GreedyState ι} {i : ι} {δ : ℤ}
    (hi : i ∈ s)
    (hΦ : (∑ j in s, |Function.update x i (x i + δ) j|) < ∑ j in s, |x j|) :
    Φ s (Function.update x i (x i + δ)) < Φ s x := by
  exact Phi_lt_of_sum_abs_lt hΦ

theorem update_opposes_of_descent
    {s : Finset ι} {x : GreedyState ι} {i : ι} {δ : ℤ}
    (hi : i ∈ s)
    (hΦ : (∑ j in s, |Function.update x i (x i + δ) j|) < ∑ j in s, |x j|) :
    x i * δ < 0 := by
  exact opposing_coord_of_descent (hi := hi) (hΦ := hΦ)

variable
  (support : Finset ι)
  (step : GreedyState ι → GreedyState ι)
  (terminal : GreedyState ι → Prop)

theorem greedy_descent_terminates
    (hdesc : ∀ x, ¬ terminal x → Φ support (step x) < Φ support x) :
    ∀ x, ∃ n, terminal (Nat.iterate step n x) := by
  have hNat : WellFounded ((· < ·) : ℕ → ℕ → Prop) := Nat.lt_wfRel.wf
  have hWF : WellFounded (InvImage ((· < ·) : ℕ → ℕ → Prop) (Φ support)) :=
    hNat.invImage (Φ support)
  intro x
  refine hWF.induction x ?_
  intro x ih
  by_cases hx : terminal x
  · exact ⟨0, hx⟩
  · have hlt : Φ support (step x) < Φ support x := hdesc x hx
    have hstep : InvImage ((· < ·) : ℕ → ℕ → Prop) (Φ support) (step x) x := hlt
    obtain ⟨n, hn⟩ := ih (step x) hstep
    exact ⟨n + 1, by simpa [Nat.iterate_succ] using hn⟩

theorem greedy_descent_correct
    (hdesc : ∀ x, ¬ terminal x → Φ support (step x) < Φ support x)
    (hfix : ∀ x, terminal x → step x = x) :
    ∀ x, ∃ n, Nat.iterate step (n + 1) x = Nat.iterate step n x := by
  intro x
  obtain ⟨n, hn⟩ := greedy_descent_terminates
    (support := support) (step := step) (terminal := terminal) hdesc x
  refine ⟨n, ?_⟩
  have hfixed : step (Nat.iterate step n x) = Nat.iterate step n x := hfix _ hn
  simpa [Nat.iterate_succ] using hfixed

end GreedyTermination

end Poincare
