import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix
import Mathlib.Analysis.NormedSpace.Basic

namespace Regge

abbrev so3 := { M : Matrix (Fin 3) (Fin 3) ℝ // Mᵀ = -M }

def zero_so3 : so3 :=
⟨0, by simp⟩

def so3_add (A B : so3) : so3 :=
⟨A.1 + B.1, by
  simp [Matrix.transpose_add, A.2, B.2]⟩

def so3_neg (A : so3) : so3 :=
⟨-A.1, by
  simp [Matrix.transpose_neg, A.2]⟩

def so3_sub (A B : so3) : so3 :=
so3_add A (so3_neg B)

def so3_bracket (A B : so3) : so3 :=
⟨A.1 ⬝ B.1 - B.1 ⬝ A.1, by
  have h1 : (A.1 ⬝ B.1)ᵀ = B.1ᵀ ⬝ A.1ᵀ := by simp
  have h2 : (B.1 ⬝ A.1)ᵀ = A.1ᵀ ⬝ B.1ᵀ := by simp
  simp [h1, h2, A.2, B.2, Matrix.mul_eq_mul, sub_eq_add_neg]⟩

end Regge
