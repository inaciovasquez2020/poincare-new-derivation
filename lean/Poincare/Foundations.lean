namespace Poincare

structure Triangulation where
  phi : Nat

def cert (T : Triangulation) : Nat := T.phi
def terminal (T : Triangulation) : Prop := cert T = 0

def nstep (step : Triangulation → Triangulation) :
  Nat → Triangulation → Triangulation
| 0, x => x
| n+1, x => nstep step n (step x)

theorem termination
  (step : Triangulation → Triangulation)
  (hdesc : ∀ T, ¬terminal T → cert (step T) < cert T) :
  ∀ T, ∃ n, terminal (nstep step n T) := by
  intro T
  classical
  refine ⟨cert T, ?_⟩
  induction (cert T) generalizing T with
  | zero =>
      simp [terminal, cert, nstep]
  | succ k ih =>
      by_cases hterm : terminal T
      · simpa [nstep] using hterm
      · have hlt := hdesc T hterm
        have := ih (step T)
        simpa [nstep] using this

end Poincare
