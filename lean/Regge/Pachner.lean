import Regge.Core
import Mathlib.Data.Finset.Basic

structure PachnerMove (M M' : SimplicialComplex) : Prop where
  support : Finset (Edge M.V)
  boundary_fixed :
    ∀ e ∉ support, M.length e = M'.length e
