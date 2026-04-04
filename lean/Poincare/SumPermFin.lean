import Mathlib

namespace Poincare

open scoped BigOperators

axiom sum_perm_fin
  {n : ℕ} (f : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
  (∑ i : Fin n, f (σ i)) = ∑ i : Fin n, f i

end Poincare
