import Regge.DSQConcreteMetricValidityPredicate

namespace Regge

/--
Extract the theorem-shaped proposition carried by a concrete DSQ
metric-validity predicate.

Boundary:
- no proof of `DSQ_METRIC_VALIDITY_THEOREM`;
- no Euclidean-realizability theorem;
- no Cayley-Menger positivity theorem;
- no volume-squared theorem;
- no Regge-geometry integration theorem.
-/
def DSQConcreteMetricValidityPredicate_theoremStatement
    (p : DSQConcreteMetricValidityPredicate) : Prop :=
  p.target.theoremStatement

end Regge
