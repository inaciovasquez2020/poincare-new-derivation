namespace Poincare

structure State where
  phi : Nat

def cert (x : State) : Nat := x.phi
def terminal (x : State) : Prop := cert x = 0

def step (x : State) : State := x

def nstep : Nat → State → State
| 0, x => x
| n+1, x => nstep n (step x)

end Poincare
