import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

universe u

abbrev Edge (V : Type u) := V × V

structure SimplicialComplex where
  V : Type u
  inst : DecidableEq V
  E : Finset (Edge V)
  length : Edge V → ℝ

attribute [instance] SimplicialComplex.inst

noncomputable def regge_action (M : SimplicialComplex) : ℝ :=
  (M.E.toList.map M.length).sum
