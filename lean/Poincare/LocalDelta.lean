import Mathlib

namespace Poincare

open scoped BigOperators

axiom sum_perm_fin
  {n : ℕ} (f : Fin n → ℤ) (σ : Equiv.Perm (Fin n)) :
  (∑ i : Fin n, f (σ i)) = ∑ i : Fin n, f i


def defect (d : ℤ) : ℤ :=
  Int.natAbs (d - 6)

def pick4 (x0 x1 x2 x3 : ℤ) : Fin 4 → ℤ
  | 0 => x0
  | 1 => x1
  | 2 => x2
  | _ => x3

def pick3 (p q r : ℤ) : Fin 3 → ℤ
  | 0 => p
  | 1 => q
  | _ => r

def pick2 (u v : ℤ) : Fin 2 → ℤ
  | 0 => u
  | _ => v

def deltaPhiOneToFourFromFamily (x : Fin 4 → ℤ) : ℤ :=
  (∑ i : Fin 4, (defect (x i + 2) - defect (x i))) + defect 4

def deltaPhiTwoToThreeFromFamilies (face : Fin 3 → ℤ) (opp : Fin 2 → ℤ) : ℤ :=
  (∑ i : Fin 3, (defect (face i - 1) - defect (face i))) +
  (∑ j : Fin 2, (defect (opp j + 1) - defect (opp j)))

def deltaPhiOneToFourFromLocal (x0 x1 x2 x3 : ℤ) : ℤ :=
  deltaPhiOneToFourFromFamily (pick4 x0 x1 x2 x3)

def deltaPhiTwoToThreeFromLocal (p q r u v : ℤ) : ℤ :=
  deltaPhiTwoToThreeFromFamilies (pick3 p q r) (pick2 u v)

def signDeltaOneToFour (x0 x1 x2 x3 : ℤ) : Ordering :=
  compare (deltaPhiOneToFourFromLocal x0 x1 x2 x3) 0

def signDeltaTwoToThree (p q r u v : ℤ) : Ordering :=
  compare (deltaPhiTwoToThreeFromLocal p q r u v) 0

theorem deltaPhiOneToFourFromFamily_perm (x : Fin 4 → ℤ) (σ : Equiv.Perm (Fin 4)) :
    deltaPhiOneToFourFromFamily (fun i => x (σ i)) = deltaPhiOneToFourFromFamily x := by
  refine congrArg (fun t => t + defect 4) ?_
  simpa [deltaPhiOneToFourFromFamily] using
    (sum_perm_fin (fun i : Fin 4 => defect (x i + 2) - defect (x i)) σ)

theorem deltaPhiTwoToThreeFromFamilies_perm
    (face : Fin 3 → ℤ) (opp : Fin 2 → ℤ)
    (σ : Equiv.Perm (Fin 3)) (τ : Equiv.Perm (Fin 2)) :
    deltaPhiTwoToThreeFromFamilies (fun i => face (σ i)) (fun j => opp (τ j)) =
      deltaPhiTwoToThreeFromFamilies face opp := by
  unfold deltaPhiTwoToThreeFromFamilies
  rw [sum_perm_fin (fun i : Fin 3 => defect (face i - 1) - defect (face i)) σ]
  rw [sum_perm_fin (fun j : Fin 2 => defect (opp j + 1) - defect (opp j)) τ]

theorem deltaPhiOneToFourFromLocal_perm
    (x0 x1 x2 x3 : ℤ) (σ : Equiv.Perm (Fin 4)) :
    deltaPhiOneToFourFromLocal
      (pick4 x0 x1 x2 x3 (σ 0))
      (pick4 x0 x1 x2 x3 (σ 1))
      (pick4 x0 x1 x2 x3 (σ 2))
      (pick4 x0 x1 x2 x3 (σ 3)) =
    deltaPhiOneToFourFromLocal x0 x1 x2 x3 := by
  simpa [deltaPhiOneToFourFromLocal] using
    deltaPhiOneToFourFromFamily_perm (pick4 x0 x1 x2 x3) σ

theorem deltaPhiTwoToThreeFromLocal_perm
    (p q r u v : ℤ) (σ : Equiv.Perm (Fin 3)) (τ : Equiv.Perm (Fin 2)) :
    deltaPhiTwoToThreeFromLocal
      (pick3 p q r (σ 0))
      (pick3 p q r (σ 1))
      (pick3 p q r (σ 2))
      (pick2 u v (τ 0))
      (pick2 u v (τ 1)) =
    deltaPhiTwoToThreeFromLocal p q r u v := by
  simpa [deltaPhiTwoToThreeFromLocal] using
    deltaPhiTwoToThreeFromFamilies_perm (pick3 p q r) (pick2 u v) σ τ

@[simp] theorem deltaPhiOneToFourFromLocal_regular6 :
    deltaPhiOneToFourFromLocal 6 6 6 6 = 10 := by
  native_decide

@[simp] theorem deltaPhiTwoToThreeFromLocal_regular6 :
    deltaPhiTwoToThreeFromLocal 6 6 6 6 6 = 5 := by
  native_decide

@[simp] theorem signDeltaOneToFour_regular6 :
    signDeltaOneToFour 6 6 6 6 = Ordering.gt := by
  native_decide

@[simp] theorem signDeltaTwoToThree_regular6 :
    signDeltaTwoToThree 6 6 6 6 6 = Ordering.gt := by
  native_decide

@[simp] theorem deltaPhiOneToFourFromLocal_nonuniform :
    deltaPhiOneToFourFromLocal 5 6 7 8 = 8 := by
  native_decide

@[simp] theorem deltaPhiTwoToThreeFromLocal_nonuniform :
    deltaPhiTwoToThreeFromLocal 5 6 7 6 8 = 3 := by
  native_decide

@[simp] theorem signDeltaOneToFour_nonuniform :
    signDeltaOneToFour 5 6 7 8 = Ordering.gt := by
  native_decide

end Poincare
