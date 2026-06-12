#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQConcretePredicateInputSurfaceBridge.lean")
text = path.read_text()

required = [
    "import Regge.DSQMetricValidityInputSurface",
    "import Regge.DSQConcreteMetricValidityPredicate",
    "def DSQConcreteMetricValidityPredicate_to_DSQMetricValidityInputSurface",
    "(p : DSQConcreteMetricValidityPredicate)",
    "DSQMetricValidityInputSurface",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required surface: {needle}")

for forbidden in [
    "DSQ_METRIC_VALIDITY_THEOREM :",
    "theorem DSQ_METRIC_VALIDITY_THEOREM",
    "axiom DSQ_METRIC_VALIDITY_THEOREM",
    "Euclidean",
    "VolumeSquared",
    "ReggeGeometryIntegration",
]:
    if forbidden in text:
        raise SystemExit(f"forbidden theorem escalation found: {forbidden}")

print("DSQ_CONCRETE_PREDICATE_INPUT_SURFACE_BRIDGE_FOUND")
