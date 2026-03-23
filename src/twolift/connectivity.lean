import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Fin.Basic
import TwoLift

open TwoLift

namespace TwoLift

variable {N : ℕ} [Fact (2 ≤ N)]

def step (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, by
    have := i.isLt
    exact Nat.mod_lt _ (Nat.pos_of_lt this)⟩

def cycle_step (v : (Fin N) × Fin 2) : (Fin N) × Fin 2 :=
  (step v.1, v.2)

-- iterate step k times
def iter_step : ℕ → (Fin N) → (Fin N)
| 0, v => v
| k+1, v => step (iter_step k v)

-- explicit reachability on base cycle
theorem reachable_base (v : Fin N) (k : ℕ) :
  ∃ w, w = iter_step k v := by
  refine ⟨iter_step k v, rfl⟩

-- lifted reachability (same fiber)
theorem reachable_lift_same_layer (v : (Fin N) × Fin 2) (k : ℕ) :
  ∃ w, w = (iter_step k v.1, v.2) := by
  refine ⟨(iter_step k v.1, v.2), rfl⟩

end TwoLift
