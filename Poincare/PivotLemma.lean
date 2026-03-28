import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Poincare

abbrev Coord := Nat

def l1NormOn (S : Finset Coord) (x : Coord → Int) : Nat :=
  ∑ j in S, Int.natAbs (x j)

def supportOn (S : Finset Coord) (x : Coord → Int) : Finset Coord :=
  S.filter (fun j => x j ≠ 0)

def PhiOn (S : Finset Coord) (x : Coord → Int) : Nat :=
  l1NormOn S x + (supportOn S x).card

def pivot (x γ : Coord → Int) : Coord → Int :=
  fun k => x k - γ k

theorem pivot_zeroes_coordinate
  {x γ : Coord → Int} {j : Coord}
  (hzero : x j - γ j = 0) :
  pivot x γ j = 0 := by
  simpa [pivot] using hzero

theorem l1_single_coordinate_reduction
  {S : Finset Coord} {x γ : Coord → Int} {j : Coord}
  (hjS : j ∈ S)
  (hunchanged : ∀ k ∈ S, k ≠ j → x k - γ k = x k)
  (hdrop : Int.natAbs (x j - γ j) = Int.natAbs (x j) - 1) :
  l1NormOn S (pivot x γ) = l1NormOn S x - 1 := by
  have hsplit₁ :
      l1NormOn S (pivot x γ) =
        (∑ k in S.erase j, Int.natAbs (pivot x γ k)) + Int.natAbs (pivot x γ j) := by
    unfold l1NormOn
    symm
    exact Finset.sum_erase_add (s := S) (a := j) (f := fun k => Int.natAbs (pivot x γ k)) hjS
  have hsplit₂ :
      l1NormOn S x =
        (∑ k in S.erase j, Int.natAbs (x k)) + Int.natAbs (x j) := by
    unfold l1NormOn
    symm
    exact Finset.sum_erase_add (s := S) (a := j) (f := fun k => Int.natAbs (x k)) hjS
  have herase :
      ∑ k in S.erase j, Int.natAbs (pivot x γ k) =
      ∑ k in S.erase j, Int.natAbs (x k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkS : k ∈ S := Finset.mem_of_mem_erase hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [pivot, hunchanged k hkS hkj]
  have hjterm : Int.natAbs (pivot x γ j) = Int.natAbs (x j) - 1 := by
    simpa [pivot] using hdrop
  rw [hsplit₁, hsplit₂, herase, hjterm]
  omega

theorem support_subset_after_pivot
  {S : Finset Coord} {x γ : Coord → Int} {j : Coord}
  (hunchanged : ∀ k ∈ S, k ≠ j → x k - γ k = x k)
  (hzero : x j - γ j = 0) :
  supportOn S (pivot x γ) ⊆ supportOn S x := by
  intro k hk
  have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
  have hkNZ : pivot x γ k ≠ 0 := (Finset.mem_filter.mp hk).2
  by_cases hkj : k = j
  · have : False := by
      simpa [supportOn, pivot, hkj, hzero] using hkNZ
    exact this.elim
  · apply Finset.mem_filter.mpr
    constructor
    · exact hkS
    · simpa [supportOn, pivot, hunchanged k hkS hkj] using hkNZ

theorem support_card_not_increase
  {S : Finset Coord} {x γ : Coord → Int} {j : Coord}
  (hunchanged : ∀ k ∈ S, k ≠ j → x k - γ k = x k)
  (hzero : x j - γ j = 0) :
  (supportOn S (pivot x γ)).card ≤ (supportOn S x).card := by
  exact Finset.card_le_card (support_subset_after_pivot hunchanged hzero)

theorem Phi_descent
  {S : Finset Coord} {x γ : Coord → Int} {j : Coord}
  (hjS : j ∈ S)
  (hunchanged : ∀ k ∈ S, k ≠ j → x k - γ k = x k)
  (hzero : x j - γ j = 0)
  (hdrop : Int.natAbs (x j - γ j) = Int.natAbs (x j) - 1) :
  PhiOn S (pivot x γ) < PhiOn S x := by
  have hl1 :
      l1NormOn S (pivot x γ) = l1NormOn S x - 1 :=
    l1_single_coordinate_reduction hjS hunchanged hdrop
  have hcard :
      (supportOn S (pivot x γ)).card ≤ (supportOn S x).card :=
    support_card_not_increase hunchanged hzero
  unfold PhiOn
  rw [hl1]
  omega

end Poincare
