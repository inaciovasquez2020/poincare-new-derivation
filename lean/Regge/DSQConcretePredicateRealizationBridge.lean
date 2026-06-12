import Regge.DSQConcretePredicateTheoremStatementBridge

namespace Regge

/--
Expose the theorem-statement realization equality carried by a concrete DSQ
metric-validity predicate.

Boundary:
- no proof of `DSQ_METRIC_VALIDITY_THEOREM`;
- no Euclidean-realizability theorem;
- no Cayley-Menger positivity theorem;
- no volume-squared theorem;
- no Regge-geometry integration theorem.
-/
def DSQConcreteMetricValidityPredicate_realizesMetricValidityStatement
    (p : DSQConcreteMetricValidityPredicate) :
    DSQConcreteMetricValidityPredicate_theoremStatement p =
      ∀ (x : p.target.surface.refinement.binding.inputShape),
        (h : p.target.surface.refinement.isValidInput x) →
          p.target.surface.metricValid x h :=
  p.target.realizesMetricValidityStatement

end Regge
