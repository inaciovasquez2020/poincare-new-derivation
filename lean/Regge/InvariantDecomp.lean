import Regge.Core
import Regge.Pachner
import Mathlib.Data.Real.Basic

def delta_regge (M M' : SimplicialComplex) : ℝ :=
  regge_action M - regge_action M'

theorem regge_split
  (M : SimplicialComplex) :
  regge_action M =
    (∑ e in M.E, M.length e * (2 * Real.pi)) -
    (∑ e in M.E, M.length e * total_angle M e) := by
  classical
  simp [regge_action, Finset.mul_sum, Finset.sum_sub_distrib, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
