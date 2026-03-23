import Mathlib.Data.Fintype.Card
import TwoLift
import TwoLift.noncollapse

open TwoLift

namespace TwoLift

variable (d R k : ℕ)

def C := configSpace d R k

lemma config_repeat
  {m : ℕ}
  (h : Fintype.card (C d R k) < m)
  (f : Fin m → C d R k) :
  ∃ i j : Fin m, i ≠ j ∧ f i = f j := by
  simpa using pigeonhole_config (d := d) (R := R) (k := k) h f

theorem pumping_step
  {m : ℕ}
  (h : Fintype.card (C d R k) < m)
  (f : Fin m → C d R k) :
  ∃ i j : Fin m, i < j ∧ f i = f j := by
  obtain ⟨i, j, hij, heq⟩ :=
    config_repeat (d := d) (R := R) (k := k) h f
  have hlt : i < j ∨ j < i := lt_or_gt_of_ne hij
  cases hlt with
  | inl hlt => exact ⟨i, j, hlt, heq⟩
  | inr hlt => exact ⟨j, i, hlt, heq.symm⟩

end TwoLift
