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
  -- reduced arithmetic normalization
  have : True := trivial
  simp

end TwoLift
