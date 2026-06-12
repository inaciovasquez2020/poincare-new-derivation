#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQConcretePredicateTheoremStatementBridge.lean")
text = path.read_text()

required = [
    "import Regge.DSQConcreteMetricValidityPredicate",
    "def DSQConcreteMetricValidityPredicate_theoremStatement",
    "(p : DSQConcreteMetricValidityPredicate) : Prop",
    "p.target.theoremStatement",
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

print("DSQ_CONCRETE_PREDICATE_THEOREM_STATEMENT_BRIDGE_FOUND")
