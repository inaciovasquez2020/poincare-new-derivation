import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Poincare

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α]

structure LocalOperator where
  support : Finset α
  act : (α → β) → α → β
  locality :
    ∀ {f g : α → β},
      (∀ x ∈ support, f x = g x) →
      ∀ x ∈ support, act f x = act g x

namespace LocalOperator

def eval (T : LocalOperator (α := α) (β := β)) (f : α → β) : α → β :=
  fun x => if hx : x ∈ T.support then T.act f x else f x

def restrict (T : LocalOperator (α := α) (β := β)) (s : Finset α) :
    LocalOperator (α := α) (β := β) where
  support := T.support ∩ s
  act := T.act
  locality := by
    intro f g h x hx
    apply T.locality
    intro y hy
    exact h y ⟨hy, by simp⟩

theorem eval_outside (T : LocalOperator (α := α) (β := β)) (f : α → β)
    {x : α} (hx : x ∉ T.support) :
    T.eval f x = f x := by
  simp [eval, hx]

end LocalOperator
end Poincare
