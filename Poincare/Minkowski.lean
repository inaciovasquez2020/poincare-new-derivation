import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Poincare

abbrev Idx := Fin 4

def eta : Idx → Idx → Int
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨i+1, hi⟩, ⟨j+1, hj⟩ => if i = j then (-1 : Int) else 0
  | _, _ => 0

@[simp] theorem eta_00 : eta ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := rfl

@[simp] theorem eta_diag_space (i : Fin 3) :
    eta ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = -1 := by
  simp [eta]

theorem eta_symm (μ ν : Idx) : eta μ ν = eta ν μ := by
  rcases μ with ⟨m, hm⟩
  rcases ν with ⟨n, hn⟩
  cases m using Nat.case <;> cases n using Nat.case <;> simp [eta]
  all_goals split_ifs <;> simp_all

end Poincare
