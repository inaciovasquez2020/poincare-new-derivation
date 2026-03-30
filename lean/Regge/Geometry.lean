import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant

def CayleyMengerDet (dSq : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  dSq.det  -- placeholder (typed, non-zero structure preserved)

def realizable (dSq : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  CayleyMengerDet dSq > 0
