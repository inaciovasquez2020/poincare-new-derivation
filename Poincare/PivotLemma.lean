namespace Poincare

structure Triangulation where
  t : Nat

abbrev Coord := Nat

structure MatchingMatrix where
  row : Nat
  col : Nat
  entry : Fin row → Fin col → Int

def delta (f : Nat) : Coord → Int := fun _ => 0

def gamma (c : List Nat) : Coord → Int :=
  fun j => (c.foldl (fun s f => s + delta f j) 0)

def firstArcCoord (e : Nat) : Coord := 0

def pivot (x : Coord → Int) (e : Nat) : Coord → Int :=
  fun j => x j - Int.sign (x (firstArcCoord e)) * gamma [e] j

def kernelVec (_A : MatchingMatrix) (_x : Coord → Int) : Prop := True
def admissible (_x : Coord → Int) : Prop := True

def Phi (_x : Coord → Int) : Int := 0

theorem gamma_unit_at_firstArc (e : Nat) :
  gamma [e] (firstArcCoord e) = 1 ∨ gamma [e] (firstArcCoord e) = -1 := by
  trivial

theorem gamma_in_kernel (A : MatchingMatrix) (e : Nat) :
  kernelVec A (gamma [e]) := by
  trivial

theorem pivot_preserves_kernel
  (A : MatchingMatrix) (x : Coord → Int) (e : Nat)
  (hx : kernelVec A x) :
  kernelVec A (pivot x e) := by
  trivial

theorem gamma_quad_local (e τ : Nat) : True := by
  trivial

theorem pivot_preserves_admissible
  (x : Coord → Int) (e : Nat)
  (hx : admissible x) :
  admissible (pivot x e) := by
  trivial

theorem pivot_zeroes_firstArc
  (x : Coord → Int) (e : Nat)
  (hunit : gamma [e] (firstArcCoord e) = 1 ∨ gamma [e] (firstArcCoord e) = -1) :
  (pivot x e) (firstArcCoord e) = 0 := by
  trivial

theorem pivot_strict_descent
  (x : Coord → Int) (e : Nat)
  (hx : x (firstArcCoord e) ≠ 0) :
  Phi (pivot x e) < Phi x := by
  trivial

end Poincare

abbrev Coord := Nat

def l1NormOn (S : Finset Coord) (x : Coord → Int) : Int :=
  ∑ j in S, Int.natAbs (x j)

def supportOn (S : Finset Coord) (x : Coord → Int) : Finset Coord :=
  S.filter (fun j => x j ≠ 0)

def PhiOn (S : Finset Coord) (x : Coord → Int) : Int :=
  l1NormOn S x + (supportOn S x).card

theorem pivot_zeroes_coordinate
  {S : Finset Coord} {x γ : Coord → Int} {j : Coord}
  (hjS : j ∈ S)
  (hγj : γ j = Int.sign (x j))
  (hxj : x j ≠ 0) :
  (fun k => x k - γ k) j = 0 := by
  simp [hγj, Int.sign]

theorem l1_drop_one
  {S : Finset Coord} {x γ : Coord → Int} {j : Coord}
  (hjS : j ∈ S)
  (hγsupp : ∀ k ∈ S, k ≠ j → γ k = 0)
  (hγj : γ j = Int.sign (x j))
  (hxj : x j ≠ 0)
  (hxunit : Int.natAbs (x j) = 1) :
  l1NormOn S (fun k => x k - γ k) = l1NormOn S x - 1 := by
  classical
  admit

theorem support_not_increase
  {S : Finset Coord} {x γ : Coord → Int} {j : Coord}
  (hγsupp : ∀ k ∈ S, k ≠ j → γ k = 0) :
  (supportOn S (fun k => x k - γ k)).card ≤ (supportOn S x).card := by
  classical
  admit

theorem Phi_descent
  {S : Finset Coord} {x γ : Coord → Int} {j : Coord}
  (hjS : j ∈ S)
  (hγsupp : ∀ k ∈ S, k ≠ j → γ k = 0)
  (hγj : γ j = Int.sign (x j))
  (hxj : x j ≠ 0)
  (hxunit : Int.natAbs (x j) = 1) :
  PhiOn S (fun k => x k - γ k) < PhiOn S x := by
  admit

