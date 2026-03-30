import Regge.Core
import Regge.Pachner

def local_angle_variation
  (M M' : SimplicialComplex) (S : Finset (Edge M.V)) : ℝ :=
  ∑ e in S, M.length e * (total_angle M e - total_angle M' e)

theorem schlafli_local_zero
  (M M' : SimplicialComplex)
  (h : PachnerMove M M') :
  local_angle_variation M M' h.support = 0 := by
  sorry

theorem regge_action_invariant
  (M M' : SimplicialComplex)
  (h : PachnerMove M M') :
  regge_action M = regge_action M' := by
  sorry
