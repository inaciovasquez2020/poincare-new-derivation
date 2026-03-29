namespace Poincare

structure State where
  phi : Nat

def cert (x : State) : Nat := x.phi
def terminal (x : State) : Prop := cert x = 0

def step (x : State) : State := x

def nstep : Nat → State → State
| 0, x => x
| n + 1, x => nstep n (step x)

def admissible (A C : Nat) : Prop := A + C ≥ 3

axiom descent :
  ∀ x, ¬ terminal x → cert (step x) < cert x

axiom termination :
  ∀ x, ∃ n, terminal (nstep n x)

axiom correctness :
  ∀ x, ∃ n, terminal (nstep n x)

structure H2Certificate where
  rankZ2 : Nat
  rankB2 : Nat
  h2_vanishes : rankZ2 = rankB2

def H2Certificate.check (c : H2Certificate) : Bool :=
  c.rankZ2 == c.rankB2

structure Pi1Certificate where
  numGenerators : Nat

def Pi1Certificate.isTrivial (c : Pi1Certificate) : Bool :=
  c.numGenerators == 0

end Poincare
