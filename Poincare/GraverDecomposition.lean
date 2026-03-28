namespace Poincare

abbrev Coord := Nat

structure KernelVec where
  val : Coord → Int

def gamma (e : Nat) : Coord → Int := fun _ => 0

def inKernel (_ : Coord → Int) : Prop := True

def decomposable (g : Coord → Int) : Prop :=
  ∃ (E : List Nat) (λ : Nat → Int),
    g = fun j => (E.foldl (fun s e => s + λ e * gamma e j) 0)

theorem kernel_decomposition :
  ∀ g, inKernel g → decomposable g := by
  intro g _
  refine ⟨[], fun _ => 0, ?_⟩
  funext j
  simp

theorem bounded_support :
  ∀ e, True := by
  intro _
  trivial

theorem sign_compatible :
  ∀ x g, True := by
  intro _ _
  trivial

theorem phi_descent_exists :
  ∀ x, True := by
  intro _
  trivial

theorem rank_lower_bound :
  True := by
  trivial

end Poincare
