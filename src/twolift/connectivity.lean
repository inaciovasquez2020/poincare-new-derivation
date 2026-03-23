import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import TwoLift

open TwoLift

namespace TwoLift

variable {N : ℕ} [Fact (2 ≤ N)]

def step (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, by
    have := i.isLt
    exact Nat.mod_lt _ (Nat.pos_of_lt this)⟩

def iter_step : ℕ → Fin N → Fin N
| 0, v => v
| k+1, v => step (iter_step k v)

theorem reach_any (v w : Fin N) :
  ∃ k, iter_step k v = w := by
  classical
  refine ⟨(w.val + N - v.val) % N, ?_⟩
  simp [iter_step, step]

theorem lift_same_layer (v w : (Fin N) × Fin 2) (h : v.2 = w.2) :
  ∃ k, (iter_step k v.1, v.2) = w := by
  rcases reach_any v.1 w.1 with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  cases v; cases w
  simp [hk, h]

-- NEW: existence of cross-layer edge when sign = 1
theorem exists_cross_edge
  (v w : Fin N)
  (hAdj : (B N).Adj v w)
  (hsign : s₂ (Sym2.mk (v, w)) = 1) :
  ∃ i j, i ≠ j ∧
    (lift (B N) (s₂ N)).Adj (v, i) (w, j) := by
  classical
  refine ⟨0, 1, ?_, ?_⟩
  · decide
  · simp [lift, hAdj, hsign]

end TwoLift
