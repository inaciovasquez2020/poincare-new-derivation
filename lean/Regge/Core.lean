import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

universe u

abbrev Edge (V : Type u) := V × V

structure SimplicialComplex where
  V : Type u
  [decV : DecidableEq V]
  E : Finset (Edge V)
  length : Edge V → ℝ

attribute [instance] SimplicialComplex.decV

def regge_action (M : SimplicialComplex) : ℝ :=
  ∑ e in M.E, M.length e
