#!/usr/bin/env python3
from pathlib import Path

path = Path("lean/Regge/DSQMetricValidityInputSurface.lean")
text = path.read_text()

required = [
    "import Regge.DSQValidityPredicateRefinement",
    "structure DSQMetricValidityInputSurface where",
    "refinement : DSQValidityPredicateRefinement",
    "metricValid :",
    "(x : refinement.binding.inputShape) →",
    "refinement.isValidInput x →",
    "def DSQ_METRIC_VALIDITY_INPUT_SURFACE : Prop :=",
    "theorem dsq_metric_validity_input_surface_open",
    "Classical.choice dsq_validity_predicate_refinement_surface_open",
]

for needle in required:
    if needle not in text:
        raise SystemExit(f"missing required surface fragment: {needle}")

for forbidden in ["axiom ", "opaque ", "sorry", "admit"]:
    if forbidden in text:
        raise SystemExit(f"forbidden proof-debt marker found: {forbidden}")

if "def DSQ_METRIC_VALIDITY_THEOREM" in text:
    raise SystemExit("forbidden premature theorem target found")

print("DSQ_METRIC_VALIDITY_INPUT_SURFACE_FOUND")
