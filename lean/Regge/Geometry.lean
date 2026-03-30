import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

open Matrix

def cayleyMenger (M : Matrix (Fin 5) (Fin 5) ℝ) : ℝ :=
  Matrix.det M

def volume_sq (dSq : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  let M : Matrix (Fin 5) (Fin 5) ℝ :=
    fun i j =>
      if i = 0 ∧ j = 0 then 0
      else if i = 0 ∨ j = 0 then 1
      else dSq ⟨i.val - 1, by decide⟩ ⟨j.val - 1, by decide⟩
  Matrix.det M / 288

def is_valid_simplex (dSq : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  0 < volume_sq dSq
