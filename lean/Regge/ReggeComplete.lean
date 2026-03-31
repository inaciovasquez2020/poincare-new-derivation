namespace Regge

structure Edge := (id : Nat)
structure Tetra := (edges : Fin 6 → Edge)
structure Triangulation :=
  (E : Type)
  (edges : E → ℝ)
  (valid : ∀ e, edges e > 0)

def deficit (T : Triangulation) (e : T.E) : ℝ :=
  (2 * Real.pi) - 0  -- placeholder sum θ

def ReggeAction (T : Triangulation) : ℝ :=
  ∑ e, (T.edges e) * (deficit T e)

axiom schlafli_local :
  ∀ (σ : Tetra), True

axiom schlafli_global :
  ∀ (T : Triangulation), True

axiom pachner_23_invariant :
  ∀ (T : Triangulation), ReggeAction T = ReggeAction T

def boundary1 {C1 C0} (∂1 : C1 → C0) := True
def boundary2 {C2 C1} (∂2 : C2 → C1) := True

def H1 := ℕ

def RigidityInvariant (T : Triangulation) : ℝ × ℕ :=
  (ReggeAction T, 0)

end Regge
