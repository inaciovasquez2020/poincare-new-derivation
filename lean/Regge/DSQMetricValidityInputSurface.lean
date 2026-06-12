import Regge.DSQValidityPredicateRefinement

namespace Regge

/--
A metric-validity input surface over the DSQ validity-predicate layer.

Boundary:
- no DSQ metric-validity theorem;
- no Euclidean-realizability theorem;
- no Cayley-Menger positivity theorem;
- no volume-squared theorem;
- no Regge-geometry integration theorem.
-/
structure DSQMetricValidityInputSurface where
  refinement : DSQValidityPredicateRefinement
  metricValid :
    (x : refinement.binding.inputShape) →
      refinement.isValidInput x →
        Prop

def DSQ_METRIC_VALIDITY_INPUT_SURFACE : Prop :=
  Nonempty DSQMetricValidityInputSurface

theorem dsq_metric_validity_input_surface_open :
    DSQ_METRIC_VALIDITY_INPUT_SURFACE := by
  let r : DSQValidityPredicateRefinement :=
    Classical.choice dsq_validity_predicate_refinement_surface_open
  exact ⟨{
    refinement := r
    metricValid := fun _ _ => True
  }⟩

end Regge
