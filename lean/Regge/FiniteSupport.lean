import Regge.Core

theorem total_angle_eq_sum_incident
  (M : SimplicialComplex) (e : Edge M.V) :
  total_angle M e = ∑ t in incidentTets M e, M.dihedralAngle e t := rfl

theorem regge_action_eq_finset
  (M : SimplicialComplex) :
  regge_action M = ∑ e in M.E, M.length e * (2 * Real.pi - total_angle M e) := rfl

theorem incidentTets_subset
  (M : SimplicialComplex) (e : Edge M.V) :
  incidentTets M e ⊆ M.T := by
  intro t ht
  exact (Finset.mem_filter.mp ht).1
