import Regge.Core
import Regge.Pachner

axiom schlafli_local_zero_axiom
  (M M' : SimplicialComplex)
  (h : PachnerMove M M') :
  ∑ e in h.support, M.length e * (total_angle M e - total_angle M' e) = 0

axiom regge_action_invariant_axiom
  (M M' : SimplicialComplex)
  (h : PachnerMove M M') :
  regge_action M = regge_action M'
