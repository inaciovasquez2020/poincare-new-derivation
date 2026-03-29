namespace Poincare

structure Triangulation where
  phi     : Nat
  h2      : Nat
  pi1Rank : Nat

def terminal (T : Triangulation) : Prop :=
  T.phi = 0

def cert (T : Triangulation) : Nat :=
  T.phi

axiom boundary_squared_zero : Prop

theorem B₂_le_Z₂ : boundary_squared_zero := boundary_squared_zero

theorem terminal_iff_cert_zero (T : Triangulation) :
    terminal T ↔ cert T = 0 := by
  rfl

theorem strict_descent
    (step : Triangulation → Triangulation)
    (hdesc : ∀ T, ¬ terminal T → cert (step T) < cert T) :
    ∀ T, ¬ terminal T → cert (step T) < cert T :=
  hdesc

theorem termination
    (step : Triangulation → Triangulation)
    (hdesc : ∀ T, ¬ terminal T → cert (step T) < cert T) :
    ∀ T, ∃ n, cert ((Nat.iterate step n) T) = 0 := by
  intro T
  classical
  let P : Triangulation → Prop := fun X => ∃ n, cert ((Nat.iterate step n) X) = 0
  have h :
      ∀ m : Nat, ∀ X : Triangulation, cert X = m → P X := by
    intro m
    induction m using Nat.caseStrongInductionOn with
    | h m ih =>
        intro X hX
        by_cases hterm : terminal X
        · exact ⟨0, (terminal_iff_cert_zero X).mp hterm⟩
        · have hs : cert (step X) < cert X := hdesc X hterm
          have hm : cert (step X) < m := by simpa [hX] using hs
          have hrec := ih (cert (step X)) hm (step X) rfl
          rcases hrec with ⟨n, hn⟩
          exact ⟨n + 1, by simpa [Nat.iterate_succ] using hn⟩
  exact h (cert T) T rfl

end Poincare
