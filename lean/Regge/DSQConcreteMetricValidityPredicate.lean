import Regge.DSQMetricValidityTheoremTarget

namespace Regge

/--
A first concrete metric-validity predicate layer.

This is intentionally weaker than a metric-validity theorem: it only
records a nontrivial carrier-side predicate that future metric-validity
statements can depend on.

Boundary:
- no proof of `DSQ_METRIC_VALIDITY_THEOREM`;
- no Euclidean-realizability theorem;
- no Cayley-Menger positivity theorem;
- no volume-squared theorem;
- no Regge-geometry integration theorem.
-/
def DSQConcreteMetricCarrierPredicate
    (c : DSQReggeComplex) : Prop :=
  0 < c.vertexCount ∧ 0 < c.edgeCount ∧ 0 < c.simplexCount

/--
A concrete metric-validity predicate package attached to a metric-validity
theorem target.
-/
structure DSQConcreteMetricValidityPredicate where
  target : DSQMetricValidityTheoremTarget
  carrierPredicate : Prop
  realizesCarrierPredicate :
    carrierPredicate =
      DSQConcreteMetricCarrierPredicate
        target.surface.refinement.binding.complex

def DSQ_CONCRETE_METRIC_VALIDITY_PREDICATE : Prop :=
  Nonempty DSQConcreteMetricValidityPredicate

theorem dsq_concrete_metric_validity_predicate_surface_open :
    DSQ_CONCRETE_METRIC_VALIDITY_PREDICATE := by
  let t : DSQMetricValidityTheoremTarget :=
    Classical.choice dsq_metric_validity_theorem_target_surface_open
  exact ⟨{
    target := t
    carrierPredicate :=
      DSQConcreteMetricCarrierPredicate
        t.surface.refinement.binding.complex
    realizesCarrierPredicate := rfl
  }⟩

end Regge
