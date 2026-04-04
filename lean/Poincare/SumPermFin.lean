import Mathlib

open scoped BigOperators

namespace Poincare

theorem sum_perm_fin
{n : ℕ} (f : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
(∑ i : Fin n, f (σ i)) = ∑ i : Fin n, f i := by
simpa using
(Fintype.sum_equiv
σ
(fun i : Fin n => f (σ i))
f
(by
intro x
simp))

end Poincare
