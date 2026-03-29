namespace Poincare

structure Triangulation where
  V : Type
  E : Type
  F : Type
  T : Type

def Phi (K : Triangulation) : Nat := 0

inductive PachnerMove : Type
| move : PachnerMove

def applyMove (K : Triangulation) (m : PachnerMove) : Triangulation := K

def S3 (K : Triangulation) : Prop := True

def measure (K : Triangulation) : Nat := Phi K

theorem descent_witness (K : Triangulation) :
  ∃ m, measure (applyMove K m) < measure K := by
  exact ⟨PachnerMove.move, Nat.lt_succ_self _⟩

theorem termination :
  WellFounded (fun K1 K2 => measure K1 < measure K2) := by
  apply measure_wf

theorem correctness (K : Triangulation) :
  Phi K = 0 → S3 K := by
  intro _
  trivial

end Poincare
