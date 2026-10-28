import Mathlib

namespace Poincare

/-- Repeat an infinite trajectory from index `i` after index `j`.
The splice is well-defined as a trajectory only when the complete states
at `i` and `j` are equal. Equality of a finite encoding is not enough. -/
def trajectorySplice {α : Type*} (states : Nat → α) (i j : Nat) :
    Nat → α :=
  fun n => if n < j then states n else states (i + (n - j))

/-- A full-state return lets an infinite trajectory be spliced into a
periodic tail while preserving every transition. This is deliberately
generic: callers must establish equality of the actual states, not merely
equality of a finite key. -/
theorem trajectorySplice_preserves_step
    {α : Type*}
    (R : α → α → Prop)
    (states : Nat → α)
    (i j : Nat)
    (hij : i < j)
    (hreturn : states i = states j)
    (hstep : ∀ n, R (states n) (states (n + 1))) :
    ∀ n, R
      (trajectorySplice states i j n)
      (trajectorySplice states i j (n + 1)) := by
  intro n
  by_cases hn : n < j
  · by_cases hnext : n + 1 < j
    · simpa [trajectorySplice, hn, hnext] using hstep n
    · have hEq : n + 1 = j := by omega
      have hJoin : states (n + 1) = states i := by
        rw [hEq, ← hreturn]
      have hstepJoin : R (states n) (states i) := by
        simpa [hEq] using (hJoin ▸ hstep n)
      simpa [trajectorySplice, hn, hnext, hEq] using hstepJoin
  · have hnge : j ≤ n := by omega
    have hnext : ¬ n + 1 < j := by omega
    have hidx : i + ((n + 1) - j) = (i + (n - j)) + 1 := by omega
    simpa [trajectorySplice, hn, hnext, hidx] using
      hstep (i + (n - j))

end Poincare
