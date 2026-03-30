import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

namespace Regge

open BigOperators

structure SimplicialComplex where
  V : Type
  inst : DecidableEq V
  faces : Finset (Finset V)
  edges : Finset (V × V)
  lengths : (V × V) → ℝ

noncomputable def deficit (T : SimplicialComplex) (e : T.V × T.V) : ℝ := 0

noncomputable def regge_action (T : SimplicialComplex) : ℝ :=
  ∑ e in T.edges, T.lengths e * deficit T e

end Regge
