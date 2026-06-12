import Regge.DSQMetricValidityInputSurface

namespace Regge

/--
A theorem-target shell for the future DSQ metric-validity theorem.

This records the exact theorem-shaped statement generated from a
`DSQMetricValidityInputSurface`.

Boundary:
- no proof of the metric-validity theorem;
- no Euclidean-realizability theorem;
- no Cayley-Menger positivity theorem;
- no volume-squared theorem;
- no Regge-geometry integration theorem.
-/
structure DSQMetricValidityTheoremTarget where
  surface : DSQMetricValidityInputSurface
  theoremStatement : Prop
  realizesMetricValidityStatement :
    theoremStatement =
      ∀ (x : surface.refinement.binding.inputShape),
        (h : surface.refinement.isValidInput x) →
          surface.metricValid x h

def DSQ_METRIC_VALIDITY_THEOREM_TARGET : Prop :=
  Nonempty DSQMetricValidityTheoremTarget

theorem dsq_metric_validity_theorem_target_surface_open :
    DSQ_METRIC_VALIDITY_THEOREM_TARGET := by
  let s : DSQMetricValidityInputSurface :=
    Classical.choice dsq_metric_validity_input_surface_open
  exact ⟨{
    surface := s
    theoremStatement :=
      ∀ (x : s.refinement.binding.inputShape),
        (h : s.refinement.isValidInput x) →
          s.metricValid x h
    realizesMetricValidityStatement := rfl
  }⟩

end Regge
