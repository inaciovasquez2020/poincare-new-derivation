import Mathlib

namespace Poincare

/--
A finite abstract model showing that recurrence of a coarse key does not
force recurrence of the full retained state, even when every transition
changes the key and the dynamics is a deterministic directed cycle.

This is a logical countermodel to the finite-key inference only. It is not
a triangulation and does not satisfy the geometric hypotheses of the
Poincare development.
-/
inductive AbstractRetainedState where
  | a0
  | b0
  | a1
  | b1
  deriving DecidableEq, Fintype

open AbstractRetainedState

/-- The deliberately coarse two-valued key. -/
def abstractKey : AbstractRetainedState → Bool
  | a0 => false
  | b0 => true
  | a1 => false
  | b1 => true

/-- A deterministic four-cycle with hidden retained-state information. -/
def abstractStep (s t : AbstractRetainedState) : Prop :=
  (s = a0 ∧ t = b0) ∨
  (s = b0 ∧ t = a1) ∨
  (s = a1 ∧ t = b1) ∨
  (s = b1 ∧ t = a0)

theorem abstract_cycle_steps :
    abstractStep a0 b0 ∧
    abstractStep b0 a1 ∧
    abstractStep a1 b1 ∧
    abstractStep b1 a0 := by
  simp [abstractStep]

theorem abstract_cycle_every_step_changes_key :
    abstractKey a0 ≠ abstractKey b0 ∧
    abstractKey b0 ≠ abstractKey a1 ∧
    abstractKey a1 ≠ abstractKey b1 ∧
    abstractKey b1 ≠ abstractKey a0 := by
  simp [abstractKey]

/--
The coarse key recurs at a0 and a1, while the complete retained states
are distinct. Thus finite-key recurrence plus non-self transitions is
insufficient, by itself, to establish full-state recurrence at the same
indices.
-/
theorem abstract_key_return_does_not_identify_state :
    abstractKey a0 = abstractKey a1 ∧ a0 ≠ a1 := by
  simp [abstractKey]

/-- The countermodel is deterministic: each state has exactly one successor. -/
theorem abstract_successor_unique :
    ∀ s t u, abstractStep s t → abstractStep s u → t = u := by
  intro s t u hst hsu
  cases s <;> simp [abstractStep] at hst hsu ⊢ <;> tauto

end Poincare
