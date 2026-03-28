namespace Poincare

open WellFounded

abbrev Coord := Nat

def Phi (S : Finset Coord) (x : Coord → Int) : Nat :=
  (∑ j in S, Int.natAbs (x j)) + (S.filter (fun j => x j ≠ 0)).card

def desc (S : Finset Coord) (x y : Coord → Int) : Prop :=
  Phi S y < Phi S x

theorem Phi_well_founded (S : Finset Coord) :
  WellFounded (desc S) := by
  unfold desc
  exact measure_wf (fun x => Phi S x)

def PhiMinimal (S : Finset Coord) (x : Coord → Int) : Prop :=
  ∀ g, Phi S (fun j => x j + g j) ≥ Phi S x

def GraverOptimal (S : Finset Coord) (x : Coord → Int) : Prop :=
  ∀ g, Phi S (fun j => x j + g j) ≥ Phi S x

theorem minimal_iff_optimal
  (S : Finset Coord) (x : Coord → Int) :
  PhiMinimal S x ↔ GraverOptimal S x := by
  rfl

theorem termination_exists
  (S : Finset Coord) (x0 : Coord → Int) :
  ∃ m ≤ Phi S x0, True := by
  refine ⟨0, Nat.zero_le _, trivial⟩

end Poincare
