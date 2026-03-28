import Mathlib

namespace Poincare

abbrev F2 := ZMod 2

section Pi1

variable {V E : ℕ}

def boundary₁Matrix
    (vertexEdgeSign : Fin V → Fin E → F2) :
    Matrix (Fin V) (Fin E) F2 :=
  fun v e => vertexEdgeSign v e

def boundaryMap {m n : ℕ} (M : Matrix (Fin m) (Fin n) F2) :
    (Fin n → F2) →ₗ[F2] (Fin m → F2) where
  toFun := fun x => M.mulVec x
  map_add' x y := by
    ext i; simp [Matrix.mulVec, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i; simp [Matrix.mulVec, Finset.mul_sum]

def Z₁ (∂₁ : Matrix (Fin V) (Fin E) F2) :
    Submodule F2 (Fin E → F2) :=
  LinearMap.ker (boundaryMap ∂₁)

structure Pi1Certificate
    (∂₁ : Matrix (Fin V) (Fin E) F2) where
  z1Rank : ℕ

noncomputable def buildPi1Certificate
    (∂₁ : Matrix (Fin V) (Fin E) F2) :
    Pi1Certificate ∂₁ where
  z1Rank := Module.finrank F2 (Z₁ ∂₁)

end Pi1

end Poincare
