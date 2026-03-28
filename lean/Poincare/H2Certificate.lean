import Mathlib

open scoped BigOperators

namespace Poincare

abbrev F2 := ZMod 2

section ChainLevel

variable {E F T : ℕ}

def boundary₂Matrix
    (edgeFaceSign : Fin E → Fin F → F2) :
    Matrix (Fin E) (Fin F) F2 :=
  fun e f => edgeFaceSign e f

def boundary₃Matrix
    (faceTetSign : Fin F → Fin T → F2) :
    Matrix (Fin F) (Fin T) F2 :=
  fun f t => faceTetSign f t

def boundaryMap {m n : ℕ} (M : Matrix (Fin m) (Fin n) F2) :
    (Fin n → F2) →ₗ[F2] (Fin m → F2) where
  toFun := fun x => M.mulVec x
  map_add' x y := by
    ext i
    simp [Matrix.mulVec, Finset.sum_add_distrib, add_mul]
  map_smul' a x := by
    ext i
    simp [Matrix.mulVec, Finset.mul_sum]

def Z₂ (∂₂ : Matrix (Fin E) (Fin F) F2) : Submodule F2 (Fin F → F2) :=
  LinearMap.ker (boundaryMap ∂₂)

def B₂ (∂₃ : Matrix (Fin F) (Fin T) F2) : Submodule F2 (Fin F → F2) :=
  LinearMap.range (boundaryMap ∂₃)

theorem boundary_squared_zero
    (∂₂ : Matrix (Fin E) (Fin F) F2)
    (∂₃ : Matrix (Fin F) (Fin T) F2)
    (h : ∂₂ ⬝ ∂₃ = 0) :
    (boundaryMap ∂₂).comp (boundaryMap ∂₃) = 0 := by
  ext x i
  have hx := congrArg (fun M : Matrix (Fin E) (Fin T) F2 => M.mulVec x) h
  simpa [boundaryMap, Matrix.mulVec_mulVec] using hx

theorem B₂_le_Z₂
    (∂₂ : Matrix (Fin E) (Fin F) F2)
    (∂₃ : Matrix (Fin F) (Fin T) F2)
    (h : ∂₂ ⬝ ∂₃ = 0) :
    B₂ ∂₃ ≤ Z₂ ∂₂ := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  change (boundaryMap ∂₂) ((boundaryMap ∂₃) y) = 0
  have hzero := boundary_squared_zero ∂₂ ∂₃ h
  simpa using LinearMap.congr_fun hzero y

def B₂InZ₂
    (∂₂ : Matrix (Fin E) (Fin F) F2)
    (∂₃ : Matrix (Fin F) (Fin T) F2)
    (h : ∂₂ ⬝ ∂₃ = 0) :
    Submodule F2 (Z₂ ∂₂) :=
  (B₂ ∂₃).comap (Z₂ ∂₂).subtype

def H₂
    (∂₂ : Matrix (Fin E) (Fin F) F2)
    (∂₃ : Matrix (Fin F) (Fin T) F2)
    (h : ∂₂ ⬝ ∂₃ = 0) :=
  Submodule.Quotient (B₂InZ₂ ∂₂ ∂₃ h)

structure H₂Certificate
    (∂₂ : Matrix (Fin E) (Fin F) F2)
    (∂₃ : Matrix (Fin F) (Fin T) F2)
    (h : ∂₂ ⬝ ∂₃ = 0) where
  z2Rank : ℕ
  b2Rank : ℕ
  h2Rank : ℕ
  rankGap : ℕ

noncomputable def buildH₂Certificate
    (∂₂ : Matrix (Fin E) (Fin F) F2)
    (∂₃ : Matrix (Fin F) (Fin T) F2)
    (h : ∂₂ ⬝ ∂₃ = 0) :
    H₂Certificate ∂₂ ∂₃ h where
  z2Rank := Module.finrank F2 (Z₂ ∂₂)
  b2Rank := Module.finrank F2 (B₂InZ₂ ∂₂ ∂₃ h)
  h2Rank := Module.finrank F2 (H₂ ∂₂ ∂₃ h)
  rankGap := Module.finrank F2 (Z₂ ∂₂) - Module.finrank F2 (B₂InZ₂ ∂₂ ∂₃ h)

theorem rank_gap_eq_h2Rank
    (∂₂ : Matrix (Fin E) (Fin F) F2)
    (∂₃ : Matrix (Fin F) (Fin T) F2)
    (h : ∂₂ ⬝ ∂₃ = 0) :
    (buildH₂Certificate ∂₂ ∂₃ h).rankGap =
      (buildH₂Certificate ∂₂ ∂₃ h).h2Rank := by
  dsimp [buildH₂Certificate]
  have hfin :=
    Submodule.finrank_quotient_add_finrank (B₂InZ₂ ∂₂ ∂₃ h)
  omega

end ChainLevel

end Poincare
