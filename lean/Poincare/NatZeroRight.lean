import Mathlib

namespace Poincare

lemma nat_add_eq_zero_right :
  ∀ a b : Nat, a + b = 0 → b = 0 := by
  intro a b h
  have := Nat.eq_zero_of_add_eq_zero h
  exact this.right

end Poincare
