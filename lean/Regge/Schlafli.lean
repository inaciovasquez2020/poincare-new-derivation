import Regge.Core
import Regge.Pachner

axiom schlafli_assembly (M : SimplicialComplex) :
  ∀ dl : Edge M.V → ℝ,
    (∀ e, e ∉ M.E → dl e = 0) →
    ∑ e in M.E, M.length e * dl e = 0

axiom regge_action_invariant (M M' : SimplicialComplex) :
  PachnerMove M M' →
  IsRealizablePath M M' →
  regge_action M = regge_action M'
