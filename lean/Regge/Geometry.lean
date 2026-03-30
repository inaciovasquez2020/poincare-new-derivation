import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

open Matrix

noncomputable def volume_sq (dSq : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  Matrix.det dSq / 288

def is_valid (dSq : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  0 < volume_sq dSq
