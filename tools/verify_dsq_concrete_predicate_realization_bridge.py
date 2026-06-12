#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQConcretePredicateRealizationBridge.lean")
text = path.read_text()

required = [
    "import Regge.DSQConcretePredicateTheoremStatementBridge",
    "def DSQConcreteMetricValidityPredicate_realizesMetricValidityStatement",
    "(p : DSQConcreteMetricValidityPredicate)",
    "DSQConcreteMetricValidityPredicate_theoremStatement p =",
    "p.target.surface.refinement.binding.inputShape",
    "p.target.surface.refinement.isValidInput x",
    "p.target.surface.metricValid x h",
    "p.target.realizesMetricValidityStatement",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required surface: {needle}")

for forbidden in [
    "def DSQ_METRIC_VALIDITY_THEOREM",
    "theorem DSQ_METRIC_VALIDITY_THEOREM",
    "axiom DSQ_METRIC_VALIDITY_THEOREM",
    "EuclideanRealizability",
    "CayleyMenger",
    "VolumeSquared",
    "ReggeGeometryIntegration",
]:
    if forbidden in text:
        raise SystemExit(f"forbidden theorem escalation found: {forbidden}")

print("DSQ_CONCRETE_PREDICATE_REALIZATION_BRIDGE_FOUND")
