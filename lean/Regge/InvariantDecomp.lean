import Regge.Core
import Regge.Pachner

def delta_regge (M M' : SimplicialComplex) : ℝ :=
  regge_action M - regge_action M'

-- structural decomposition (no axioms)
theorem regge_split
  (M : SimplicialComplex) :
  regge_action M =
    ∑ e in M.E, M.length e * (2 * Real.pi) -
    ∑ e in M.E, M.length e * total_angle M e := by
  simp [regge_action, Finset.mul_sum, Finset.sum_sub_distrib]
