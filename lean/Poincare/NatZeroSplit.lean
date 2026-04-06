import Mathlib

namespace Poincare

lemma nat_add_eq_zero_split :
  ∀ a b : Nat, a + b = 0 → a = 0 ∧ b = 0 := by
  intro a b h
  exact Nat.eq_zero_of_add_eq_zero h

end Poincare
