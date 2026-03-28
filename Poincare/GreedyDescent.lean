import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Poincare

abbrev Coord := Nat

def supportOn (S : Finset Coord) (x : Coord → Int) : Finset Coord :=
  S.filter (fun j => x j ≠ 0)

def Phi (S : Finset Coord) (x : Coord → Int) : Nat :=
  (∑ j in S, Int.natAbs (x j)) + (supportOn S x).card

def SignCompat (g h : Coord → Int) : Prop :=
  ∀ j, h j ≠ 0 → Int.sign (h j) = Int.sign (g j)

def overlap (S : Finset Coord) (x h : Coord → Int) : Nat :=
  ((supportOn S x) ∩ (supportOn S h)).card

def Opposes (x h : Coord → Int) : Prop :=
  ∃ j, x j * h j < 0

def argminOverlap? (S : Finset Coord) (x : Coord → Int) :
    List (Coord → Int) → Option (Coord → Int)
| [] => none
| h :: hs =>
    let cand := argminOverlap? hs
    if hOpp : Opposes x h then
      match cand with
      | none => some h
      | some h' =>
          if overlap S x h ≤ overlap S x h' then some h else some h'
    else
      cand

def selectIndex? (S : Finset Coord) (x h : Coord → Int) : Option Coord :=
  ((S.filter (fun j => x j * h j < 0)).min?' id)

def step (S : Finset Coord) (gs : List (Coord → Int)) (x : Coord → Int) : Coord → Int :=
  match argminOverlap? S x gs with
  | none => x
  | some h => fun j => x j + h j

def run (S : Finset Coord) (gs : List (Coord → Int)) : Nat → (Coord → Int) → (Coord → Int)
| 0, x => x
| n+1, x => run S gs n (step S gs x)

def PhiMinimal (S : Finset Coord) (gs : List (Coord → Int)) (x : Coord → Int) : Prop :=
  step S gs x = x

theorem opposing_coord_of_descent
  {S : Finset Coord} {x g : Coord → Int}
  (hdesc : Phi S (fun j => x j + g j) < Phi S x) :
  ∃ j, x j * g j < 0 := by
  sorry

theorem opposing_coord_of_conformal_sum
  {S : Finset Coord} {x g : Coord → Int} {gs : List (Coord → Int)}
  (hsum : ∀ j, g j = (gs.foldl (fun s h => s + h j) 0))
  (hcompat : ∀ h ∈ gs, SignCompat g h)
  (hdesc : Phi S (fun j => x j + g j) < Phi S x) :
  ∃ h ∈ gs, ∃ j, x j * h j < 0 := by
  sorry

theorem step_decreases_or_fixed
  {S : Finset Coord} {gs : List (Coord → Int)} {x : Coord → Int} :
  (step S gs x = x) ∨ Phi S (step S gs x) < Phi S x := by
  sorry

theorem run_terminates
  {S : Finset Coord} {gs : List (Coord → Int)} (x : Coord → Int) :
  ∃ m ≤ Phi S x, PhiMinimal S gs (run S gs m x) := by
  sorry

theorem run_total_correct
  {S : Finset Coord} {gs : List (Coord → Int)} (x : Coord → Int) :
  ∃ m ≤ Phi S x,
    PhiMinimal S gs (run S gs m x) ∧
    ∀ n < m, Phi S (run S gs (n+1) x) < Phi S (run S gs n x) := by
  sorry

end Poincare
