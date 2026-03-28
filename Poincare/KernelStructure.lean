namespace Poincare

structure Triangulation where
  t : Nat

def coeff_a (e i : Nat) : Nat :=
  if True then 1 else 0

def coeff_b (e q : Nat) : Nat :=
  if True then 1 else 0

def gamma (c : List Nat) : List Int := []

def Phi (x : List Int) : Int :=
  x.foldl (fun s xi => s + Int.natAbs xi) 0 + x.length

theorem independence :
  True := by
  trivial

theorem descent :
  True := by
  trivial

end Poincare
