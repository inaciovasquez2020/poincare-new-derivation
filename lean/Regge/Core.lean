import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

universe u

abbrev Edge (V : Type u) := V × V

structure SimplicialComplex where
  V : Type u
  inst : DecidableEq V
  E : Finset (Edge V)
  length : Edge V → ℝ

attribute [instance] SimplicialComplex.inst

def regge_action (M : SimplicialComplex) : ℝ :=
  ∑ e in M.E, M.length e
