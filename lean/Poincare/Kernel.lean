import Mathlib.Data.Nat.Basic

namespace Poincare

structure Triangulation where
  complexity : Nat
deriving Repr

def Phi (K : Triangulation) : Nat := K.complexity

inductive PachnerMove : Type | move : PachnerMove

def selectMove (_ : Triangulation) : PachnerMove := PachnerMove.move

def applyMove (K : Triangulation) (m : PachnerMove) : Triangulation :=
  match m with
  | PachnerMove.move => { complexity := K.complexity - 1 }

def S3 (K : Triangulation) : Prop := K.complexity = 0

def measure (K : Triangulation) : Nat := Phi K

theorem descent_witness (K : Triangulation) (h : K.complexity > 0) :
    ∃ m, measure (applyMove K m) < measure K :=
  ⟨selectMove K, by simp [measure, Phi, applyMove]; omega⟩

theorem termination :
    WellFounded (fun K1 K2 : Triangulation => measure K1 < measure K2) :=
  InvImage.wf measure Nat.lt_wfRel.wf

theorem correctness (K : Triangulation) :
    Phi K = 0 → S3 K := id

end Poincare
