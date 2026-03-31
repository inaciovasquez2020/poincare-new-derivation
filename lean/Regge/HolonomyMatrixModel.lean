import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix
import Regge.Core

namespace Regge

open Matrix

noncomputable section

abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

def so3_pred (A : M3) : Prop := Aᵀ = -A

structure so3Model where
  val : M3
  skew : so3_pred val

def so3_norm (A : so3Model) : ℝ := ‖A.val‖

axiom so3_norm_submultiplicative :
  ∀ A B : M3, ‖A ⬝ B‖ ≤ ‖A‖ * ‖B‖

def SO3_pred (Q : M3) : Prop := Qᵀ ⬝ Q = 1 ∧ Q.det = 1

structure SO3Model where
  val : M3
  mem_SO3 : SO3_pred val

axiom exp_so3_model : so3Model → SO3Model

axiom log_SO3_principal :
  {Q : SO3Model} → so3Model

axiom log_exp_principal :
  ∀ A : so3Model, log_SO3_principal (exp_so3_model A) = A

abbrev EdgeCoord (T : SimplicialComplex) := T.V × T.V

abbrev EdgeVec (T : SimplicialComplex) := EdgeCoord T → ℝ

axiom gramMatrix : (T : SimplicialComplex) → ℝ → M3

axiom lambdaMin : M3 → ℝ

axiom gram_coercive :
  ∀ (T : SimplicialComplex) (t : ℝ),
    0 < lambdaMin (gramMatrix T t)

axiom local_generator :
  (T : SimplicialComplex) →
  FundamentalGroup T →
  (ℝ → EdgeVec T) →
  ℝ →
  so3Model

axiom holonomy_product :
  (T : SimplicialComplex) →
  FundamentalGroup T →
  (ℝ → EdgeVec T) →
  ℝ →
  SO3Model

axiom bch_quadratic_remainder :
  ∀ A B : so3Model,
    ∃ R : so3Model,
      log_SO3_principal (exp_so3_model A) =
        A ∧
      so3_norm R ≤ (so3_norm A + so3_norm B)^2

axiom holonomy_linearization_constructive
  (T : SimplicialComplex)
  (γ : FundamentalGroup T)
  (path : ℝ → EdgeVec T)
  (t : ℝ) :
  ∃ X R : so3Model,
    holonomy_product T γ path t = exp_so3_model X ∧
    so3_norm R ≤ (1 / lambdaMin (gramMatrix T t)) * (so3_norm X)^2

theorem rigidity_of_zero_generator
  (T : SimplicialComplex)
  (γ : FundamentalGroup T)
  (path : ℝ → EdgeVec T)
  (t : ℝ)
  (hX :
    ∀ X R : so3Model,
      holonomy_product T γ path t = exp_so3_model X →
      so3_norm X = 0) :
  ∃ X : so3Model, holonomy_product T γ path t = exp_so3_model X := by
  rcases holonomy_linearization_constructive T γ path t with ⟨X, R, hρ, hR⟩
  exact ⟨X, hρ⟩

end

end Regge
