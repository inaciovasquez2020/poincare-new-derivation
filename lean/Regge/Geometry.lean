import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant

def CayleyMengerDet (dSq : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  dSq.det

def realizable (dSq : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  CayleyMengerDet dSq > 0
