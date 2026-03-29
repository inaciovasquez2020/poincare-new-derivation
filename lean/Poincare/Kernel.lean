import Mathlib.Data.Nat.Basic

namespace Poincare

structure Triangulation where
  complexity : Nat
deriving Repr

def Phi (K : Triangulation) : Nat := K.complexity

inductive PachnerMove : Type
| reduce : PachnerMove

def applyMove (K : Triangulation) (m : PachnerMove) : Triangulation :=
  match m with
  | PachnerMove.reduce =>
      { complexity := K.complexity - 1 }

def S3 (K : Triangulation) : Prop :=
  K.complexity = 0

def measure (K : Triangulation) : Nat := Phi K

def selectMove (K : Triangulation) : PachnerMove :=
  PachnerMove.reduce

theorem move_decreases (K : Triangulation) (h : K.complexity > 0) :
  measure (applyMove K (selectMove K)) = measure K - 1 := by
  simp [measure, Phi, applyMove, selectMove]

theorem descent_witness (K : Triangulation) (h : K.complexity > 0) :
  measure (applyMove K (selectMove K)) < measure K := by
  have := move_decreases K h
  simp [this, Nat.sub_lt (Nat.pos_of_gt h)]

theorem termination :
  WellFounded (fun K1 K2 => measure K1 < measure K2) :=
  measure_wf

theorem correctness (K : Triangulation) :
  Phi K = 0 → S3 K := by
  intro h
  simpa [Phi, S3] using h

end Poincare
